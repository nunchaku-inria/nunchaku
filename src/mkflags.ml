 let () =
   let major, minor =
     Scanf.sscanf Sys.ocaml_version "%u.%u"
       (fun major minor -> major, minor)
   in
   let after_4_3 = (major, minor) >= (4, 3) in
   let opt_flags_file = open_out "opt.flags" in
   let common_flags_file = open_out "common.flags" in
   if after_4_3 then (
     output_string opt_flags_file "(-O2)\n";
     output_string common_flags_file "(-color always)\n";
   ) else (
     output_string opt_flags_file "()\n";
     output_string common_flags_file "()\n";
   );
   close_out opt_flags_file;
   close_out common_flags_file;
   ()
