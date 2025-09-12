import subprocess
import tempfile
import os
import re

def convert_declare_var_to_fun(sygus_content: str) -> str:
    """
    Converts all (declare-var x Int) to (declare-fun x () Int) in the given SyGuS content.
    """
    pattern = r'\(declare-var\s+([^\s\)]+)\s+([^\s\)]+)\)'
    replacement = r'(declare-fun \1 () \2)'
    return re.sub(pattern, replacement, sygus_content)

# def constraints_to_assert(sygus_content: str) -> str:
#     """
#     Replaces all SyGuS constraint lines with a single SMT-LIB assertion
#     of the form:
#     (assert (not (and ...constraints...)))
#     Returns the modified SyGuS content.
#     """
#     # Find all constraint lines (one per line)
#     constraint_lines = re.findall(r'^\s*\(constraint\s+.+?\)\s*$', sygus_content, re.MULTILINE)
#     if not constraint_lines:
#         return sygus_content  # No constraints to convert

#     # Extract the inner expressions of each constraint
#     inner_constraints = [re.search(r'\(constraint\s+(.+?)\)', c, re.DOTALL).group(1).strip() for c in constraint_lines]

#     # Create the combined assertion
#     combined_assertion = "(assert (not\n    (and " + "\n         ".join(inner_constraints) + "\n    )\n))"

#     # Remove all constraint lines from the content
#     content_wo_constraints = re.sub(r'^\s*\(constraint\s+.+?\)\s*$', '', sygus_content, flags=re.MULTILINE)

#     # Insert the combined assertion at the position of the first constraint line
#     first_constraint_pos = min(sygus_content.find(line) for line in constraint_lines)
#     modified_content = (
#         content_wo_constraints[:first_constraint_pos].rstrip() +
#         "\n" + combined_assertion + "\n" +
#         content_wo_constraints[first_constraint_pos:].lstrip()
#     )

#     return modified_content

def constraints_to_assert(sygus_content: str) -> str:
    """
    Replaces all SyGuS constraint blocks (even multi-line, nested) with a single SMT-LIB assertion
    of the form:
    (assert (not (and ...constraints...)))
    Returns the modified SyGuS content.
    """
    constraints = []
    content_wo_constraints = sygus_content
    pattern = r'\(constraint'
    idx = 0
    while True:
        match = re.search(pattern, content_wo_constraints[idx:])
        if not match:
            break
        start = idx + match.start()
        # Find the matching closing parenthesis for this constraint
        stack = []
        i = start
        while i < len(content_wo_constraints):
            if content_wo_constraints[i] == '(':
                stack.append('(')
            elif content_wo_constraints[i] == ')':
                stack.pop()
                if not stack:
                    break
            i += 1
        constraint_block = content_wo_constraints[start:i+1]
        # Extract the inner part
        inner = constraint_block[len('(constraint'): -1].strip()
        constraints.append(inner)
        # Remove this constraint from the content
        content_wo_constraints = content_wo_constraints[:start] + content_wo_constraints[i+1:]
        idx = start  # Continue searching after the removed block

    if not constraints:
        return sygus_content  # No constraints to convert

    # Create the combined assertion
    combined_assertion = "(assert (not\n    (and " + "\n         ".join(constraints) + "\n    )\n))"

    # Insert the combined assertion at the position of the first constraint
    insert_pos = sygus_content.find('(constraint')
    if insert_pos == -1:
        modified_content = content_wo_constraints.rstrip() + "\n" + combined_assertion + "\n"
    else:
        modified_content = (
            content_wo_constraints[:insert_pos].rstrip() +
            "\n" + combined_assertion + "\n" +
            content_wo_constraints[insert_pos:].lstrip()
        )

    return modified_content

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
    problem_file = "./example-pair/1.sy"
    candidate_solution = """((define-fun max2 ((x Int) (y Int)) Int (ite (<= y x) x y)))"""  # Example solution
    output = check_sygus_solution(problem_file, candidate_solution)
    print(f"Output: {output}")