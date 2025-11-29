import re

def convert_declare_var_to_fun(sygus_content: str) -> str:
    """
    Converts all (declare-var x Int) to (declare-fun x () Int) in the given SyGuS content.
    Handles optional spaces after '(' and before ')'.
    """
    pattern = r'\(\s*declare-var\s+([^\s\)]+)\s+([^\s\)]+)\s*\)'
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
        else:
            modified_lines.append(line)
    return "".join(modified_lines)

def add_check_sat_statement(content: str) -> str:
    """
    Adds (check-sat) statement.
    """
    return content + "\n(check-sat)\n"

def add_get_model_statement(content: str) -> str:
    """
    Adds (get-model) statement.
    """
    return content + "\n(get-model)\n"

def remove_check_synth(content: str) -> str:
    """
    Removes (check-synth) statement.
    """
    pattern = r'\(check-synth\)'
    return re.sub(pattern, '', content)

def get_constraints(sygus_content: str) -> list[str]:
    """
    Extracts all SyGuS constraints (even multi-line, nested) from the given content.
    Returns a list of constraint strings.
    """
    constraints = []
    pattern = r'\(constraint'
    idx = 0
    while True:
        match = re.search(pattern, sygus_content[idx:])
        if not match:
            break
        start = idx + match.start()
        # Find the matching closing parenthesis for this constraint
        stack = []
        i = start
        while i < len(sygus_content):
            if sygus_content[i] == '(':
                stack.append('(')
            elif sygus_content[i] == ')':
                stack.pop()
                if not stack:
                    break
            i += 1
        constraint_block = sygus_content[start:i+1]
        # Extract the inner part
        inner = constraint_block[len('(constraint'): -1].strip()
        constraints.append(inner)
        idx = i + 1  # Continue searching after this block
    return constraints

def add_get_value_statements(content: str, constraints: list[str]) -> str:
    """
    Adds (get-value ...) statements for each constraint.
    """
    get_value_statements = "\n".join([f"(get-value ({constraint}))" for constraint in constraints])
    return content + "\n" + get_value_statements + "\n"

def constraints_to_assert(content: str, constraints: list[str]) -> str:
    """
    Replaces all SyGuS constraint blocks (even multi-line, nested) with a single SMT-LIB assertion
    of the form:
    (assert (not (and ...constraints...)))
    Returns the modified SyGuS content.
    """
    content_wo_constraints = content

    for constraint in constraints:
        # Remove this constraint from the content
        pattern = r'\(constraint\s+' + re.escape(constraint) + r'\s*\)'
        content_wo_constraints = re.sub(pattern, '', content_wo_constraints, count=1)
    
    if not constraints:
        return content  # No constraints to convert

    # Create the combined assertion
    combined_assertion = (
        "(assert (not\n"
        "    (and " + " ".join(constraints) + "\n"
        "    )\n"
        "))\n"
    )
    modified_content = content_wo_constraints.rstrip() + "\n" + combined_assertion + "\n"

    return modified_content

# def convert_sygus_to_smt2(sygus_spec: str, solution: str) -> str:
#     """
#     Converts the given SyGuS content to SMT-LIB format.
#     """
#     modified = remove_check_synth(sygus_spec)
#     modified = replace_synth_fun_with_solution(modified, solution)
#     modified = convert_declare_var_to_fun(modified)
#     constraints = get_constraints(sygus_spec)
#     modified = constraints_to_assert(modified, constraints)
#     modified = add_check_sat_statement(modified)
#     modified = add_get_value_statements(modified, constraints)
#     modified = add_get_model_statement(modified)
    
#     return modified

def remove_constraints(content: str, constraints: list[str]) -> str:
    """
    Removes all (constraint ...) blocks corresponding to the provided constraint inners.
    """
    content_wo_constraints = content
    for constraint in constraints:
        pattern = r'\(constraint\s+' + re.escape(constraint) + r'\s*\)'
        content_wo_constraints = re.sub(pattern, '', content_wo_constraints, count=1)
    return content_wo_constraints

def insert_after_last_declare_fun(content: str, solution: str) -> str:
    """
    Inserts the solution string after the last (declare-fun ...) line in the content.
    If no (declare-fun ...) is found, appends at the end.
    """
    lines = content.splitlines(keepends=True)
    last_idx = -1
    for idx, line in enumerate(lines):
        if line.strip().startswith("(declare-fun"):
            last_idx = idx
    if last_idx == -1:
        # No declare-fun found, append at end
        return content.rstrip() + "\n\n" + solution + "\n"
    # Insert after the last declare-fun line
    return (
        "".join(lines[:last_idx + 1])
        + "\n"
        + solution
        + "\n"
        + "".join(lines[last_idx + 1:])
    )

def remove_synth_fun_blocks(content: str) -> str:
    """
    Removes all (synth-fun ...) blocks (including grammar definitions) from the content.
    """
    lines = content.splitlines(keepends=True)
    modified_lines = []
    skipping = False
    paren_count = 0

    for line in lines:
        if not skipping and "(synth-fun" in line:
            # Start skipping lines until the synth-fun block ends
            skipping = True
            paren_count = line.count('(') - line.count(')')
            continue
        if skipping:
            paren_count += line.count('(') - line.count(')')
            if paren_count <= 0:
                skipping = False
            continue
        else:
            modified_lines.append(line)
    return "".join(modified_lines)

def convert_sygus_to_smt2_per_constraint(sygus_spec: str, solution: str) -> list[str]:
    """
    For each SyGuS constraint, produce a separate SMT2 content that asserts only that single
    constraint negated, i.e., (assert (not <constraint>)).
    Returns a list of SMT2 contents, one per constraint. If there are no constraints, returns [].
    """
    constraints = get_constraints(sygus_spec)
    if not constraints:
        return []

    # Build a base (no constraints, replaced synth-fun, converted declares)
    base = remove_check_synth(sygus_spec)
    # base = replace_synth_fun_with_solution(base, solution)
    base = remove_synth_fun_blocks(base)
    base = convert_declare_var_to_fun(base)
    base = remove_constraints(base, constraints).rstrip()
    base = insert_after_last_declare_fun(base, solution)

    outputs: list[str] = []
    for c in constraints:
        # Single-constraint assertion
        single = base + "\n" + "(assert (not\n" + f"    {c}\n" + "))\n"
        single = add_check_sat_statement(single)
        single = add_get_model_statement(single)
        outputs.append(single)
    return outputs