def get_func_signature(text: str, is_sol: bool):
    """
    Extracts function name, argument list, and return type from SyGuS spec or solution.
    If is_sol is True, expects (define-fun ...), else expects (synth-fun ...).
    Returns (func_name, arg_list, return_type).
    arg_list is a list of tuples: [(arg_name, arg_type), ...]
    """
    import re
    if is_sol:
        # (define-fun funcName ((argName argType) ...) returnType ...)
        pattern = r'\(define-fun\s+([^\s\(\)]+)\s+\((.*?)\)\s+([^\s\(\)]+)'
    else:
        # (synth-fun funcName ((argName argType) ...) returnType)
        pattern = r'\(synth-fun\s+([^\s\(\)]+)\s+\((.*?)\)\s+([^\s\(\)]+)\s*\)'
    match = re.search(pattern, text, re.DOTALL)
    if not match:
        return "", [], ""
    func_name = match.group(1)
    args_str = match.group(2)
    return_type = match.group(3)
    arg_list = []
    for arg_match in re.finditer(r'\(([^\s\(\)]+)\s+([^\s\(\)]+)\)', args_str):
        arg_list.append((arg_match.group(1), arg_match.group(2)))
    return func_name, arg_list, return_type

def add_return_type_to_solution(solution: str, problem_spec: str) -> str:
    """
    Adds the return type from the problem specification to the solution if missing.
    The return type is inserted after the argument list in (define-fun ...).
    """
    # Get return type from spec
    _, _, spec_return_type = get_func_signature(problem_spec, is_sol=False)
    if not spec_return_type:
        # nothing to insert
        return solution

    lower_sol = solution  # keep original casing/spacing
    idx = lower_sol.find('(define-fun')
    if idx == -1:
        return solution  # no define-fun found

    # find the '(' that starts the arg list (the first '(' after the function name)
    # but safer: find the '(' following the function name
    # move cursor to after "(define-fun"
    cursor = idx + len('(define-fun')
    # skip whitespace
    while cursor < len(lower_sol) and lower_sol[cursor].isspace():
        cursor += 1
    # skip function name token
    while cursor < len(lower_sol) and not lower_sol[cursor].isspace() and lower_sol[cursor] != '(':
        cursor += 1
    # skip whitespace until '(' of arg list
    while cursor < len(lower_sol) and lower_sol[cursor].isspace():
        cursor += 1
    if cursor >= len(lower_sol) or lower_sol[cursor] != '(':
        return solution  # malformed, bail

    # Now cursor points at '(' that opens the arg list. Find matching closing ')'
    depth = 0
    p = cursor
    while p < len(lower_sol):
        ch = lower_sol[p]
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0:
                args_close_idx = p  # index of ')'
                break
        p += 1
    else:
        # unmatched parentheses, bail
        return solution

    # after args_close_idx, find the next non-whitespace character
    q = args_close_idx + 1
    while q < len(lower_sol) and lower_sol[q].isspace():
        q += 1

    # If next char is '(' then return type is missing (body starts immediately).
    # If next char is not '(' (e.g., 'I' for "Int"), assume return type present.
    if q < len(lower_sol) and lower_sol[q] == '(':
        # insert " <return_type>" right after args_close_idx
        insert_pos = args_close_idx + 1  # insert before the whitespace we skipped
        updated = (
            solution[:insert_pos] +
            f' {spec_return_type}' +
            solution[insert_pos:]
        )
        print(f"WARNING: Missing return type. Added return type '{spec_return_type}' to solution.")
        return updated

    # else return type likely present; do nothing
    return solution


spec = """
(set-logic LIA)

; Function to synthesize.  When no grammar is specified, a pre-defined grammar is used.
(synth-fun max2 ((x Int) (y Int) (z Int)) Int
)

(declare-var x Int)
(declare-var y Int)

; Constraints
(constraint (>= (max2 x y) x))
(constraint (>= (max2 x y) y))
(constraint (or (= x (max2 x y))
				(= y (max2 x y))))


(check-synth)
"""

solution = """
;solution
(define-fun max2 ((x Int) (y Int) (z Int)) Int (ite (>= (+ x (* (- 1) y)) 0) x y))

"""

updated_solution = add_return_type_to_solution(solution, spec)
print("Updated Solution:")
print(updated_solution)
