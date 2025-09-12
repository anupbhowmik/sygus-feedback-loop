import subprocess
import tempfile
import os

from convert.utils import convert_declare_var_to_fun, constraints_to_assert

def check_sygus_solution(problem_file: str, solution: str) -> str:
    print(f"Reading problem file: {problem_file}")
    with open(problem_file, "r") as f:
        content = f.read()

    # Convert (declare-var ...) to (declare-fun ...)
    content = convert_declare_var_to_fun(content)

    # Convert constraints to a single assertion
    content = constraints_to_assert(content)

    # Replace the entire line containing (synth-fun with the solution
    lines = content.splitlines(keepends=True)
    modified_lines = []
    replaced = False
    skip_next = False
    for line in lines:
        if skip_next:
            skip_next = False
            continue
        if not replaced and "(synth-fun" in line:
            modified_lines.append(solution + "\n")
            replaced = True
            skip_next = True  # Skip the next line (assumed to be ')')
        else:
            # Replace (check-synth) with (check-sat)
            if "(check-synth)" in line:
                modified_lines.append(line.replace("(check-synth)", "(check-sat)"))
            else:
                modified_lines.append(line)
    modified = "".join(modified_lines)


    with tempfile.NamedTemporaryFile(suffix=".smt2", delete=False, mode="w", encoding="utf-8") as tmp:
        tmp.write(modified)
        tmp.flush()
        tmp_name = tmp.name

    print(f"Temporary file created at: {tmp_name}")
    # print the file content for debugging
    print("\n==============================\n\n")
    with open(tmp_name, "r") as f:
        print("Solution file content:")
        print(f.read())
    print("\n==============================\n\n")

    try:
        result = subprocess.run(
            ["cvc5", tmp_name],
            capture_output=True,
            text=True
        )
        print("Subprocess finished.")
        print("stdout:")
        print(result.stdout)
        print("stderr:")
        print(result.stderr)
    except Exception as e:
        print(f"Error running cvc5: {e}")
        return f"Error: {e}"
    finally:
        if os.path.exists(tmp_name):
            os.remove(tmp_name)
            print(f"Temporary file {tmp_name} deleted.")

    return result.stdout.lower()


if __name__ == "__main__":
    problem_file = "./example-pair/max.sy"
    candidate_solution = """(define-fun max2 ((x Int) (y Int)) Int (ite (>= (+ x (* (- 1) y)) 0) x y))"""  # Example solution
    output = check_sygus_solution(problem_file, candidate_solution)
    print(f"Output: {output}")