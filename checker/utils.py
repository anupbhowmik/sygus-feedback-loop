import subprocess
import tempfile
import os

def check_sygus_solution(smt2Spec: str, iter: int, output_file: str = None) -> str:
    '''
    Check the given SyGuS solution using cvc5.
    If output_file is provided, write the modified SMT2 content to that file.
    
    Returns:
    - cvc5 output as a string
    - If there's an error running cvc5, returns the error message.
    '''
    tmp_name = None

    if output_file:
        os.makedirs(os.path.dirname(output_file), exist_ok=True)
    if output_file and output_file.endswith(".smt2"):
        output_file = output_file[:-5] + f"_iter{iter}.smt2"
    elif output_file:
        output_file = output_file + f"_iter{iter}.smt2"
    
    if output_file:
        with open(output_file, "w", encoding="utf-8") as out_f:
            out_f.write(smt2Spec)
        tmp_name = output_file
        print(f"Output written to: {output_file}")
    else:
        with tempfile.NamedTemporaryFile(suffix=".smt2", delete=False, mode="w", encoding="utf-8") as tmp:
            tmp.write(smt2Spec)
            tmp.flush()
            tmp_name = tmp.name
        print(f"Temporary file created at: {tmp_name}")

    # print the file content for debugging
    # print("\n==============================\n\n")
    # with open(tmp_name, "r") as f:
    #     print("Solution file content:")
    #     print(f.read())
    # print("\n==============================\n\n")

    try:
        result = subprocess.run(
            ["cvc5", tmp_name, "--produce-models"],
            capture_output=True,
            text=True
        )
        print("Subprocess finished.")

    except Exception as e:
        print(f"Error running cvc5: {e}")
        return f"Error: {e}"
    finally:
        if not output_file and tmp_name and os.path.exists(tmp_name):
            os.remove(tmp_name)
            print(f"Temporary file {tmp_name} deleted.")

    return result.stdout.lower()

