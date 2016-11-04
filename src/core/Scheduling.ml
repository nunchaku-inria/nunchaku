
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Scheduling of sub-processes} *)

module E = CCResult

(*$inject
  module E = CCResult
*)

type 'a or_error = ('a, exn) CCResult.t

let section = Utils.Section.make "scheduling"

module MVar = struct
  type 'a t = {
    mutable v: 'a;
    lock: Mutex.t;
  }
  let make v = {v; lock=Mutex.create(); }
  let with_ v ~f =
    Mutex.lock v.lock;
    CCFun.finally ~f ~h:(fun () -> Mutex.unlock v.lock)
  let get v = with_ v ~f:(fun () -> v.v)
  let set v x = with_ v ~f:(fun () -> v.v <- x)
  let update ~f v =
    with_ v
      ~f:(fun () ->
        let x, res = f v.v in
        v.v <- x;
        res)
end

module Fut = struct
  type 'a final_state =
    | Stopped
    | Done of 'a
    | Fail of exn

  (* bag of tasks to execute one after the other *)
  type tasks_bag = (unit -> unit) Queue.t

  type 'a on_res_callback = tasks_bag -> 'a final_state -> unit

  type 'a t = {
    lock: Mutex.t;
    cond: Condition.t;
    mutable on_res: (tasks_bag -> 'a final_state -> unit) list;
    mutable state : 'a final_state option; (* none=running *)
  }

  let with_ t ~f =
    Mutex.lock t.lock;
    CCFun.finally ~h:(fun () -> Mutex.unlock t.lock) ~f

  (* fixpoint: do all the tasks in [q], until [q] is empty *)
  let run_queue_ q =
    while not (Queue.is_empty q) do
      try Queue.pop q ()
      with _ -> ()
    done

  let apply_in0_ q f = Queue.push f q
  let apply_in1_ q f x = Queue.push (fun () -> f x) q
  let apply_in2_ q f x y = Queue.push (fun () -> f x y) q

  let set_res ~idempotent t res =
    (* tasks to do without a lock *)
    let q = Queue.create() in
    with_ t
      ~f:(fun () -> match t.state with
        | Some Stopped -> ()
        | Some _ ->
          if not idempotent then failwith "future already done"
        | None ->
          t.state <- Some res;
          Condition.broadcast t.cond;
          (* apply each callback, but in [q], outside of the lock *)
          List.iter (fun f -> apply_in2_ q f q res) t.on_res;
      );
    (* now execute the tasks *)
    run_queue_ q;
    ()

  let set_done t x = set_res ~idempotent:false t (Done x)

  let set_fail t e = set_res ~idempotent:false t (Fail e)

  let stop t = set_res ~idempotent:true t Stopped

  let get t =
    with_ t
      ~f:(fun () -> match t.state with
        | Some s -> s
        | None ->
          Condition.wait t.cond t.lock;
          match t.state with
            | None -> assert false
            | Some s -> s)

  let is_done t = with_ t ~f:(fun () -> t.state <> None)

  let on_res t ~f =
    let q = Queue.create() in
    with_ t
      ~f:(fun () -> match t.state with
        | None -> t.on_res <- f :: t.on_res
        | Some res -> apply_in2_ q f q res);
    run_queue_ q;
    ()

  let return x = {
    on_res=[];
    lock=Mutex.create();
    cond=Condition.create();
    state=Some (Done x);
  }

  let map f x =
    let y = {
      on_res=[];
      lock=Mutex.create();
      cond=Condition.create();
      state=None;
    } in
    on_res x
      ~f:(fun q res -> match res with
        | Stopped -> apply_in1_ q stop y
        | Done x ->
          apply_in0_ q
            (fun () ->
              try set_done y (f x)
              with e -> set_fail y e)
        | Fail e -> apply_in2_ q set_fail y e);
    on_res y
      ~f:(fun q res -> match res with
        | Stopped -> apply_in1_ q stop x (* propagate "stop" *)
        | _ -> ());
    y

  type 'a partial_result =
    | P_done of 'a
    | P_fail of exn

  let make ?(on_res=[]) f =
    let fut = {
      on_res;
      lock=Mutex.create();
      cond=Condition.create();
      state=None;
    } in
    (* task to run in a thread *)
    let compute_and_set () =
      let res =
        try P_done (f ())
        with e -> P_fail e
      in
      match res with
      | P_done x -> set_done fut x
      | P_fail e -> set_fail fut e
    in
    (* spawn thread to run the job *)
    let _ = Thread.create compute_and_set () in
    fut
end

(*$=
  (Fut.Done 42) ( \
    let t = Fut.make (fun () -> Thread.delay 0.2; 42) in \
    Fut.get t)
*)

(*$=
  Fut.Stopped ( \
    let t = Fut.make (fun () -> Thread.delay 0.2; 42) in \
    Fut.stop t; \
    Fut.get t)
*)

(*$=
  (Fut.Fail Pervasives.Exit) ( \
    let t = Fut.make (fun () -> Thread.delay 0.2; raise Pervasives.Exit) in \
    Fut.get t)
*)

(*$=
  (Fut.Fail Pervasives.Exit) ( \
    let t = Fut.make (fun () -> 0) |> Fut.map (fun _ -> raise Exit) in \
    Fut.get t)
*)

(*$=
  (Fut.Done ()) ( \
    let t = Fut.make (fun () -> 0) |> Fut.map (fun _ -> ()) in \
    Fut.on_res t ~f:(fun _ -> raise Exit); \
    Fut.get t)
*)

type process_status = int

(* make sure that we are a session leader; that is, our children die if we die *)
let ensure_session_leader =
  let thunk = lazy (
    if not Sys.win32 && not Sys.cygwin
    then ignore (Unix.setsid ())
  ) in
  fun () -> Lazy.force thunk

(* create a new active process by running [cmd] and applying [f] on it *)
let popen ?(on_res=[]) cmd ~f =
  Utils.debugf ~lock:true ~section 3
    "@[<2>start sub-process@ `@[%s@]`@]" (fun k->k cmd);
  ensure_session_leader ();
  ignore (Unix.sigprocmask Unix.SIG_BLOCK [13]); (* block sigpipe *)
  (* spawn subprocess *)
  let stdout, p_stdout = Unix.pipe () in
  let stderr, p_stderr = Unix.pipe () in
  let p_stdin, stdin = Unix.pipe () in
  Unix.set_close_on_exec stdout;
  Unix.set_close_on_exec stderr;
  Unix.set_close_on_exec stdin;
  let stdout = Unix.in_channel_of_descr stdout in
  let stdin = Unix.out_channel_of_descr stdin in
  let pid = Unix.create_process
      "/bin/sh" [| "/bin/sh"; "-c"; cmd |] p_stdin p_stdout p_stderr in
  Unix.close p_stdout;
  Unix.close p_stdin;
  Unix.close p_stderr;
  Utils.debugf ~lock:true ~section 3
    "@[<2>pid %d -->@ sub-process `@[%s@]`@]" (fun k -> k pid cmd);
  (* cleanup process *)
  let cleanup q _ =
    Fut.apply_in0_ q
      (fun () ->
         Utils.debugf ~lock:true ~section 3 "cleanup subprocess %d" (fun k->k pid);
         (try Unix.kill pid 15 with _ -> ());
         close_out_noerr stdin;
         close_in_noerr stdout;
         (try Unix.close stderr with _ -> ());
         (try Unix.kill pid 9 with _ -> ()); (* just to be sure *)
         Utils.debugf ~lock:true ~section 3 "subprocess %d cleaned" (fun k->k pid);
      )
  in
  Fut.make ~on_res:(cleanup :: on_res)
    (fun () ->
       try
         let x = f (stdin, stdout) in
         let _, res = Unix.waitpid [Unix.WUNTRACED] pid in
         let res = match res with
           | Unix.WEXITED i | Unix.WSTOPPED i | Unix.WSIGNALED i -> i
         in
         Utils.debugf ~lock:true ~section 3
           "@[<2>sub-process %d done;@ command was `@[%s@]`@]"
           (fun k->k pid cmd);
         E.return (x,res)
       with e ->
         E.fail e
    )

(*$T
  (try ignore (popen "ls /tmp" ~f:(fun _ -> ()) |> Fut.get); true with _ -> false)
*)

(*$=
  (Fut.Done (E.Ok ("coucou\n", 0))) \
    (popen "echo coucou" ~f:(fun (_,oc) -> CCIO.read_all oc) |> Fut.get)
*)

type shortcut =
  | Shortcut
  | No_shortcut

module Task = struct
  type ('a, 'res) inner = {
    prio: int; (* priority. The lower, the more urgent *)
    slice: float; (* fraction of time allotted to the task *)
    f: (deadline:float -> unit -> ('a * shortcut) Fut.t);
    post: ('a -> 'res);
  }
  (** Task consisting in running [f arg], obtaining a result. After [f]
      returns, [post] is applied to the result to obtain a value
      of type ['res] *)

  type 'res t =
    | Task : ('a, 'res) inner -> 'res t

  let of_fut ?(prio=50) ?(slice=1.) f =
    Task { prio; f; slice; post=CCFun.id; }

  let make ?prio ?slice f =
    of_fut ?prio ?slice
      (fun ~deadline () -> Fut.make (fun () -> f ~deadline ()))

  let compare_prio (Task t1) (Task t2) = Pervasives.compare t1.prio t2.prio

  let map ~f (Task t_i) =
    Task {t_i with post=(fun x -> f (t_i.post x)); }
end

(* task currently running *)
type 'res running_task =
  | R_task :
      int * (* unique ID *)
      ('a, 'res) Task.inner *
      ('a * shortcut) Fut.t ->
      'res running_task

type 'a run_result =
  | Res_one of 'a
  | Res_list of 'a list
  | Res_fail of exn

type 'res pool = {
  j: int;
  deadline: float;
  total_alloted_time: float; (* total time, from creation of pool to deadline *)
  mutable task_id: int;
  mutable todo: 'res Task.t list;
  mutable active : 'res running_task list;
  mutable pool_state : 'res run_result;
  lock: Mutex.t;
  cond: Condition.t;
}

let kill_rtask_ (R_task (_,_,fut)) = Fut.stop fut

let with_ p ~f =
  Mutex.lock p.lock;
  CCFun.finally ~h:(fun () -> Mutex.unlock p.lock) ~f

(* remove running task by its ID *)
let rec remove_rtask_ id l = match l with
  | [] -> []
  | R_task (id', _, _) :: tl when id=id' -> tl
  | t :: tl -> t :: remove_rtask_ id tl

(* return a running task.
   precondition: p is locked
   postcondition: new task is started, added to p, and p is unlocked *)
let start_task p t =
  let id = p.task_id in
  p.task_id <- id + 1;
  let (Task.Task t_inner) = t in
  (* adjust deadline according to task.slice: take the minimum of
     the global deadline, and *)
  let deadline =
    let now = Unix.gettimeofday() in
    let deadline' = now +. (p.total_alloted_time *. t_inner.Task.slice) in
    min p.deadline deadline'
  in
  Utils.debugf ~section 5 "@[<2>actual deadline is %.2f (slice: %.2f)@]"
    (fun k->k deadline t_inner.Task.slice);
  let fut = t_inner.Task.f ~deadline () in
  let r_task = R_task (id, t_inner, fut) in
  p.active <- r_task :: p.active;
  Mutex.unlock p.lock;
  (* ensure that after completion, the task is removed and the pool's
     state is updated *)
  Fut.on_res fut
    ~f:(fun _ res ->
      with_ p
        ~f:(fun () ->
          p.active <- remove_rtask_ id p.active;
          begin match res, p.pool_state with
            | Fut.Done (x, No_shortcut), Res_list l ->
              begin
                try
                  let y = t_inner.Task.post x in
                  p.pool_state <- Res_list (y::l)
                with e ->
                  p.pool_state <- Res_fail e
              end
            | Fut.Done (x, Shortcut), Res_list _ ->
              begin
                try
                  let y = t_inner.Task.post x in
                  p.pool_state <- Res_one y
                with e ->
                  p.pool_state <- Res_fail e
              end
            | Fut.Fail e, Res_list _ ->
              p.pool_state <- Res_fail e;
            | Fut.Stopped, _
            | _, (Res_one _ | Res_fail _) -> ()
          end;
          (* awake the main thread, if required *)
          Condition.broadcast p.cond)
    );
  ()

(* main function for running threads *)
let rec run_pool pool =
  Mutex.lock pool.lock;
  match pool.todo, pool.active, pool.pool_state with
    | _, _, (Res_one _ | Res_fail _) ->
        (* return now *)
        Utils.debug ~lock:true ~section 2 "stop active tasks...";
        Mutex.unlock pool.lock;
        List.iter kill_rtask_ pool.active;
        pool.pool_state
    | [], [], _ ->
        Utils.debug ~lock:true ~section 2 "all tasks done";
        Mutex.unlock pool.lock;
        pool.pool_state
    | task :: todo_tl, _, Res_list _ ->
        if List.length pool.active < pool.j
        then (
          Utils.debugf ~lock:true ~section 2
            "start new task (active: %d / j=%d / todo: %d)"
            (fun k->k (List.length pool.active) pool.j (List.length todo_tl));
          (* run new task *)
          pool.todo <- todo_tl;
          start_task pool task; (* releases lock *)
        ) else (
          (* wait for something to happen *)
          Utils.debugf ~lock:true ~section 2
            "waiting (max number of active tasks / todo: %d)..."
            (fun k->k (1+List.length todo_tl));
          Condition.wait pool.cond pool.lock;
          Mutex.unlock pool.lock;
        );
        run_pool pool
    | [], _::_, Res_list _ ->
        (* wait for something to happen *)
        Utils.debug ~lock:true ~section 2 "waiting for tasks to finish...";
        Condition.wait pool.cond pool.lock;
        Mutex.unlock pool.lock;
        (* check again *)
        run_pool pool

let run ~j ~deadline tasks =
  if j < 1 then invalid_arg "Scheduling.run";
  Utils.debugf ~lock:true ~section 1
    "@[<2>%d tasks to run (j=%d)...@]" (fun k->k (List.length tasks) j);
  let pool = {
    todo=List.sort Task.compare_prio tasks; (* sort by increasing 'prio' *)
    active=[];
    pool_state = Res_list [];
    task_id=0;
    deadline;
    total_alloted_time=(deadline -. Unix.gettimeofday());
    j;
    lock=Mutex.create();
    cond=Condition.create();
  } in
  run_pool pool

(*$=
  (Res_one 5) ( \
    let mk i = Task.make \
      (fun ~deadline:_ () -> if i=5 then i, Shortcut else i, No_shortcut) in \
    run ~j:3 ~deadline:5. CCList.(1 -- 10 |> map mk))
*)

(*$=
  (Res_one 5) ( \
    let mk i = Task.make \
      (fun ~deadline:_ () -> Thread.delay (float i *. 0.1); \
                 if i=5 then i, Shortcut else i, No_shortcut) in \
    run ~j:3 ~deadline:5. CCList.(1 -- 10 |> map mk))
*)

(*$=
  (Res_fail Exit) ( \
    let mk i = Task.make (fun ~deadline:_ () -> if i=5 then raise Exit else i, No_shortcut) in \
    run ~j:3 ~deadline:5. CCList.(1 -- 10 |> map mk))
*)

(*$=
  (Res_list CCList.(1--10)) ( \
    let mk i = Task.make (fun ~deadline:_ () -> i, No_shortcut) in \
    let res = run ~j:3 ~deadline:5. CCList.(1 -- 10 |> map mk) in \
    match res with Res_list l -> Res_list (List.sort Pervasives.compare l) | x->x)
*)
