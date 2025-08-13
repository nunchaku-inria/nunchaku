from enum import Enum
import os
import shutil
import yaml

class Verdict(Enum):
    SAT = 1
    UNSAT = 2

    def property_file(self) -> str:
        if self == Verdict.SAT:
            return "sat.prp"
        elif self == Verdict.UNSAT:
            return "unsat.prp"
        else:
            assert False

    def expected_verdict(self) -> bool:
        if self == Verdict.SAT:
            return True
        elif self == Verdict.UNSAT:
            return False
        else:
            assert False


def mk_task(verdict: Verdict, file: str):
    return {
        "format_version": "2.0",
        "input_files": [file],
        "properties": [{
            "property_file": verdict.property_file(),
            "expected_verdict":  verdict.expected_verdict()
        }]
    }

def mk_tasks(verdict: Verdict, input_dir: str, output_dir: str):
    for filename in os.listdir(input_dir):
        root_name, ext = os.path.splitext(filename)
        if ext == ".nun":
            task = mk_task(verdict, os.path.join("..", "..", input_dir, filename))
            with open(os.path.join(output_dir, f"{root_name}.yml"), "w") as out:
                out.write(yaml.dump(task))

def main():
    shutil.rmtree("tasks/sat", ignore_errors=True)
    os.makedirs("tasks/sat", exist_ok=True)
    mk_tasks(Verdict.SAT, "../tests/sat", "tasks/sat")
    open("tasks/sat/sat.prp", "w").close()

    shutil.rmtree("tasks/unsat", ignore_errors=True)
    os.makedirs("tasks/unsat", exist_ok=True)
    mk_tasks(Verdict.UNSAT, "../tests/unsat", "tasks/unsat")
    open("tasks/unsat/unsat.prp", "w").close()

if __name__ == "__main__":
    main()
