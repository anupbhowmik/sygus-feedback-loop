import re

def extract_solution_using_parenthesis(response: str, VERBOSE: str) -> list[str]:
    """
    Extracts SyGuS solutions from the LLM response.
    If multiple solutions are present, extracts all of them.
    """
    solutions = []
    start_pos = 0

    while True:
        # Find the next occurrence of (define-fun
        start_idx = response.find("(define-fun", start_pos)
        if start_idx == -1:
            break

        # Find the matching closing parenthesis
        paren_count = 0
        end_idx = start_idx
        found_complete = False

        for i in range(start_idx, len(response)):
            if response[i] == '(':
                paren_count += 1
            elif response[i] == ')':
                paren_count -= 1
                if paren_count == 0:
                    end_idx = i + 1
                    found_complete = True
                    break

        if found_complete and paren_count == 0:
            solution = response[start_idx:end_idx].strip()
            solutions.append(solution)
            start_pos = end_idx
        else:
            if VERBOSE:
                print(f"SYNTAX-ERROR: incomplete/missing closing parenthesis.")
            # Attempt to fix by balancing parentheses
            partial = response[start_idx:]
            open_paren = partial.count('(')
            close_paren = partial.count(')')
            if open_paren > close_paren:
                # Add missing closing parens
                fixed = partial + (')' * (open_paren - close_paren))
            elif close_paren > open_paren:
                # Remove excess closing parens
                excess = close_paren - open_paren
                fixed = partial
                for _ in range(excess):
                    idx = fixed.rfind(')')
                    if idx != -1:
                        fixed = fixed[:idx] + fixed[idx+1:]
            else:
                fixed = partial
            solutions.append(fixed.strip())
            break

    if not solutions and "(define-fun" not in response and VERBOSE:
        print("SYNTAX-ERROR: No solution found: '(define-fun' not present in response.")

    return solutions


def extract_solution_from_response(response: str, VERBOSE: str) -> list[str]:
    """
    Extracts SyGuS solutions from the LLM response.
    If multiple solutions are present, extracts all of them and ensures parentheses are balanced.
    Falls back to extract_solution_using_parenthesis if no wrapped solution is found.
    [won't need if tool calling is used]
    """
    solutions = []
    # Extract all wrapped solutions
    pattern = r'<<<SOLUTION>>>\s*(.*?)\s*<<<END>>>'
    wrapped_solutions = re.findall(pattern, response, re.DOTALL)

    if wrapped_solutions:
        if VERBOSE:
            print(f"Found {len(wrapped_solutions)} wrapped solution(s) in LLM response.")
        solutions = refine_solution_from_wrapped(wrapped_solutions, VERBOSE)
    else:
        if VERBOSE:
            print("No wrapped solution found. Attempting to extract solution directly using parentheses.")
        solutions = extract_solution_using_parenthesis(response, VERBOSE)

    return solutions

def refine_solution_from_wrapped(wrapped_solutions: list[str], VERBOSE: bool) -> list[str]:
    """
    Refines solutions extracted from wrapped markers by ensuring they are complete S-expressions.
    Returns a list of refined solutions.
    """    
    solutions = []
    for wrapped in wrapped_solutions:
        # Find the next occurrence of (define-fun
        start_idx = wrapped.find("(define-fun")
        if start_idx == -1:
            if VERBOSE:
                print("SYNTAX-ERROR: '(define-fun' not present in wrapped solution.")
            continue

        # Find the matching closing parenthesis
        paren_count = 0
        end_idx = start_idx
        found_complete = False

        for i in range(start_idx, len(wrapped)):
            if wrapped[i] == '(':
                paren_count += 1
            elif wrapped[i] == ')':
                paren_count -= 1
                if paren_count == 0:
                    end_idx = i + 1
                    found_complete = True
                    break

        if found_complete and paren_count == 0:
            solution = wrapped[start_idx:end_idx].strip()
            solutions.append(solution)
        else:
            if VERBOSE:
                print(f"SYNTAX-ERROR: incomplete/missing closing parenthesis in wrapped solution.")
            # Attempt to fix by balancing parentheses
            partial = wrapped[start_idx:]
            open_paren = partial.count('(')
            close_paren = partial.count(')')
            if open_paren > close_paren:
                fixed = partial + (')' * (open_paren - close_paren))
            elif close_paren > open_paren:
                excess = close_paren - open_paren
                fixed = partial
                for _ in range(excess):
                    idx = fixed.rfind(')')
                    if idx != -1:
                        fixed = fixed[:idx] + fixed[idx+1:]
            else:
                fixed = partial
            solutions.append(fixed.strip())
            if VERBOSE:
                print(f"WARNING: Unbalanced parentheses. Fixed solution to balance parentheses\n")

    if not solutions and VERBOSE:
        print("WARNING: No solution found in LLM response.\n")

    return solutions

def main():
    # Example usage
    response = """
    Here is the solution you requested:
    <<<SOLUTION>>>
    (define-fun f ((x Int)) Int
        (+ x 1))
    <<<END>>>

    (define-fun f ((x Int)) Int
        (+ x 2))
    <<<END>>>
    Let me know if you need anything else.
    """

    VERBOSE = True
    solutions = extract_solution_from_response(response, VERBOSE)
    for sol in solutions:
        print("Extracted Solution:")
        print(sol)

if __name__ == "__main__":
    main()