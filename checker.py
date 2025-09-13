import subprocess
import tempfile
import os
import sys

from convert.utils import convert_declare_var_to_fun, constraints_to_assert, replace_synth_fun_with_solution

def check_sygus_solution(problem_file: str, solution: str, output_file: str = None) -> str:
    print(f"Reading problem file: {problem_file}")
    with open(problem_file, "r") as f:
        content = f.read()

    # Convert (declare-var ...) to (declare-fun ...)
    content = convert_declare_var_to_fun(content)

    # Convert constraints to a single assertion
    content = constraints_to_assert(content)

    # Replace (synth-fun ...) with the provided solution and (check-synth) with (check-sat)
    modified = replace_synth_fun_with_solution(content, solution)

    tmp_name = None
    if output_file:
        with open(output_file, "w", encoding="utf-8") as out_f:
            out_f.write(modified)
        tmp_name = output_file
        print(f"Output written to: {output_file}")
    else:
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
        if not output_file and tmp_name and os.path.exists(tmp_name):
            os.remove(tmp_name)
            print(f"Temporary file {tmp_name} deleted.")

    return result.stdout.lower()


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Check SyGuS solution using cvc5.")
    parser.add_argument("--p", required=True, help="Input SyGuS problem file")
    parser.add_argument("--s", required=True, help="Candidate solution as a string")
    parser.add_argument("--o", "-o", help="Output file name (optional, if not given, use temp file)", default=None)

    args = parser.parse_args()

    output = check_sygus_solution(args.p, args.s, args.o)
    print(f"Output: {output}")