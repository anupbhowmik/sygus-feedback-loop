import subprocess
import tempfile
import os

def check_sygus_solution(problem_file: str, solution: str) -> str:
    print(f"Reading problem file: {problem_file}")
    with open(problem_file, "r") as f:
        content = f.read()

    print("Original problem content:")
    print(content)

    # Replace synth-fun with candidate solution
    modified = content.replace("(synth-fun", "(define-fun")  # naive replace (assuming only one synth-fun), refine later
    modified += "\n" + solution

    print("Modified problem content to be checked:")
    print(modified)

    with tempfile.NamedTemporaryFile(suffix=".sl", delete=False, mode="w", encoding="utf-8") as tmp:
        tmp.write(modified)
        tmp.flush()
        tmp_name = tmp.name

    print(f"Temporary file created at: {tmp_name}")
    # print the file content for debugging
    with open(tmp_name, "r") as f:
        print("Solution file content:")
        print(f.read())

    try:
        result = subprocess.run(
            ["cvc5", "--lang=sygus2", tmp_name],
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
    problem_file = "./problems/1.sl"
    candidate_solution = """(define-fun max2 ((x Int) (y Int)) Int (ite (>= (+ x (* (- 1) y)) 0) x y))"""  # Example solution
    output = check_sygus_solution(problem_file, candidate_solution)
    print(f"Output: {output}")