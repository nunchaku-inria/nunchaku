import benchexec.result as result
import benchexec.tools.template


class Tool(benchexec.tools.template.BaseTool2):
    """
    Tool info for the Nunchaku model finder.
    """

    def executable(self, tool_locator):
        return tool_locator.find_executable("nunchaku")

    def name(self):
        return "nunchaku"

    def project_url(self):
        return "https://github.com/nunchaku-inria/nunchaku"

    def version(self, executable):
        return "1"

    def cmdline(self, executable, options, task, rlimits):
        if rlimits.cputime:
            options += [f"--timeout={rlimits.cputime}"]
        return [executable] + options + [task.single_input_file]

    def determine_result(self, run):
        """
        @return: status of Kissat after executing a run
        """

        status = None

        for line in run.output:
            if line.startswith("SAT"):
                status = result.RESULT_TRUE_PROP
            elif line.startswith("UNSAT"):
                status = result.RESULT_FALSE_PROP
            elif line.startswith("UNKNOWN"):
                status = result.RESULT_UNKNOWN

        if not status:
            status = result.RESULT_ERROR
        return status
