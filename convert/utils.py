import re

def convert_declare_var_to_fun(sygus_content: str) -> str:
    """
    Converts all (declare-var x Int) to (declare-fun x () Int) in the given SyGuS content.
    """
    pattern = r'\(declare-var\s+([^\s\)]+)\s+([^\s\)]+)\)'
    replacement = r'(declare-fun \1 () \2)'
    return re.sub(pattern, replacement, sygus_content)

def replace_synth_fun_with_solution(content: str, solution: str) -> str:
    """
    Replace the (synth-fun ...) block (including grammar definitions) with the provided solution,
    and replace (check-synth) with (check-sat).

    Assumptions:
    1. There is only one (synth-fun ...) block in the content
    2. Ignores grammar definitions after synth-fun
    """
    lines = content.splitlines(keepends=True)
    modified_lines = []
    replaced = False
    skipping = False
    paren_count = 0

    for line in lines:
        if not replaced and "(synth-fun" in line:
            # Start skipping lines until the synth-fun block ends
            skipping = True
            paren_count = line.count('(') - line.count(')')
            modified_lines.append(solution + "\n")
            replaced = True
            continue
        if skipping:
            paren_count += line.count('(') - line.count(')')
            if paren_count <= 0:
                skipping = False
            continue
        if "(check-synth)" in line:
            modified_lines.append(line.replace("(check-synth)", "(check-sat)"))
        else:
            modified_lines.append(line)
    return "".join(modified_lines)

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
