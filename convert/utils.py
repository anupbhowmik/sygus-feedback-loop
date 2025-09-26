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
        else:
            modified_lines.append(line)
    return "".join(modified_lines)

def replace_check_synth_with_check_sat(content: str) -> str:
    """
    Replace (check-synth) with (check-sat) in the given content.
    """
    return content.replace("(check-synth)", "(check-sat)")

def add_get_model_statement(content: str) -> str:
    """
    Adds (get-model) statement before (check-sat) in the given content.
    If (check-sat) is not found, appends (get-model) at the end.
    """
    return content + "\n(get-model)\n"

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


# def constraints_to_assert(sygus_content: str) -> str:
#     """
#     Replaces all SyGuS constraint blocks (even multi-line, nested) with a single SMT-LIB assertion
#     of the form:
#     (assert (not (and ...constraints...)))
#     Returns the modified SyGuS content.
#     """
#     constraints = get_constraints(sygus_content)
#     content_wo_constraints = sygus_content

#     for constraint in constraints:
#         # Remove this constraint from the content
#         pattern = r'\(constraint\s+' + re.escape(constraint) + r'\s*\)'
#         content_wo_constraints = re.sub(pattern, '', content_wo_constraints, count=1)
    
#     if not constraints:
#         return sygus_content  # No constraints to convert

#     # for each of the constraints, add boolean variables so that we can track which constraint fails
#     bool_vars = [f"b{i+1}" for i in range(len(constraints))]
#     bool_decls = "\n".join([f"(declare-fun {var} () Bool)" for var in bool_vars])
    
#     bool_asserts = "\n".join([f"(assert (= {var} {constraint}))" for var, constraint in zip(bool_vars, constraints)])
#     combined_assertion = bool_decls + "\n" + bool_asserts + "\n\n"

#     combined_assertion += (
#         "(assert (not\n"
#         "    (and " + " ".join(bool_vars) + "\n"
#         "    )\n"
#         "))\n"
#     )

#     # Insert the combined assertion at the position of the first constraint
#     insert_pos = sygus_content.find('(constraint')
#     if insert_pos == -1:
#         modified_content = content_wo_constraints.rstrip() + "\n" + combined_assertion + "\n"
#     else:
#         modified_content = (
#             content_wo_constraints[:insert_pos].rstrip() +
#             "\n" + combined_assertion + "\n" +
#             content_wo_constraints[insert_pos:].lstrip()
#         )

#     return modified_content

def constraints_to_assert(sygus_content: str) -> str:
    """
    Replaces all SyGuS constraint blocks (even multi-line, nested) with a single SMT-LIB assertion
    of the form:
    (assert (not (and ...constraints...)))
    And adds (get-value ...) statements for each constraint.
    Returns the modified SyGuS content.
    """
    constraints = get_constraints(sygus_content)
    content_wo_constraints = sygus_content

    for constraint in constraints:
        # Remove this constraint from the content
        pattern = r'\(constraint\s+' + re.escape(constraint) + r'\s*\)'
        content_wo_constraints = re.sub(pattern, '', content_wo_constraints, count=1)
    
    if not constraints:
        return sygus_content  # No constraints to convert

    # Create the combined assertion
    combined_assertion = (
        "(assert (not\n"
        "    (and " + " ".join(constraints) + "\n"
        "    )\n"
        "))\n"
    )

    # call replace_check_synth_with_check_sat
    content_wo_constraints = replace_check_synth_with_check_sat(content_wo_constraints)
    # TODO: need to drop check-synth and add get-model

    # Add get-value statements for each constraint
    get_value_statements = "\n".join([f"(get-value ({constraint}))" for constraint in constraints])
    combined_assertion += "\n" + get_value_statements + "\n"

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