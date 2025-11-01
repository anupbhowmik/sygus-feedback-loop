import re
def get_synth_func_name(problem_spec: str) -> str:
    import re
    match = re.search(r'\(synth-fun\s+([^\s\(\)]+)', problem_spec)
    if match:
        return match.group(1)
    return ""

def fix_synth_func_names(problem_spec: str, solutions: list) -> list:
    """
    Replace the synth function name in each solution with the correct one from the problem spec.
    Returns a list of fixed solutions.
    """
    correct_func_name = get_synth_func_name(problem_spec)
    fixed_solutions = []
    for solution in solutions:
        # Match (define-fun ... or (synth-fun ...
        match = re.match(r'\((define-fun|synth-fun)\s+([^\s\(\)]+)', solution)
        if match:
            func_type, found_name = match.groups()
            if found_name != correct_func_name:
                # Replace the function name with the correct one
                fixed_solution = re.sub(
                    r'(\((define-fun|synth-fun)\s+)([^\s\(\)]+)',
                    r'\1' + correct_func_name,
                    solution,
                    count=1
                )
                fixed_solutions.append(fixed_solution)
            else:
                fixed_solutions.append(solution)
        else:
            fixed_solutions.append(solution)
    return fixed_solutions


def main():

    # Example usage
    problem_spec = """
    (synth-fun myFunc ((x Int) (y Int)) Int)
    (declare-var x Int)
    (declare-var y Int)
    (constraint (= (myFunc x y) (+ x y)))
    """
    responses = [
        "(define-fun wrongFunc ((x Int) (y Int)) Int (+ x y))",
        "(synth-fun anotherWrongFunc ((x Int) (y Int)) Int (+ x y))",
        "(define-fun myFunc ((x Int) (y Int)) Int (+ x y))"
    ]
    fixed_solutions = fix_synth_func_names(problem_spec, responses)
    for sol in fixed_solutions:
        print(sol)

if __name__ == "__main__":
    main()