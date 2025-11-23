from convert import get_constraints
import re

def generate_init_prompt(problem_spec: str) -> str:
    """
    Generates the initial prompt for the LLM given a SyGuS problem specification.
    """
    init_prompt = f"You are a helpful assistant that generates SyGuS solutions based on the given problem specification. "
    init_prompt += prepare_format_instruction()
    init_prompt += example_pair_context()
    init_prompt += f"You will be provided with a SyGuS problem specification. \
Your task is to generate a valid SyGuS solution that adheres to the constraints and requirements outlined in the specification.\
Ensure that your solution is syntactically correct and logically consistent with the problem statement.\n\n{problem_spec}."
    init_prompt += "\n\nMake sure to use the provided tools to generate solution.\n"
    return init_prompt

def example_pair_context():
    """
    Returns example pair of (problem_spec, solution) formatted per prepare_format_instruction.
    """
    problem_spec_max = """(set-logic LIA)

; Function to synthesize.  When no grammar is specified, a pre-defined grammar is used.
(synth-fun max2 ((x Int) (y Int)) Int
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
    solution_max = """
(define-fun max2 ((x Int) (y Int)) Int (ite (>= (+ x (* (- 1) y)) 0) x y))
"""

    problem_spec_small = """(set-logic LIA)

(synth-fun f ((x Int) (y Int)) Int)

(declare-var x Int)
(declare-var y Int)
(constraint (= (f x y) (f y x)))
(constraint (and (<= x (f x y)) (<= y (f x y))))

(check-synth)
"""
    solution_small = """
(define-fun f ((x Int) (y Int)) Int (ite (<= y x) x y))
"""

    example_pair_context = (
        "Here are some examples of SyGuS problem specifications and their corresponding solutions as context, you don't need to solve them, they are given just as examples.\n\n"
    )
    example_pair_context += f"Problem Specification 1:\n{problem_spec_max}\n"
    example_pair_context += f"Solution 1:\n{solution_max}\n\n"
    example_pair_context += f"Problem Specification 2:\n{problem_spec_small}\n"
    example_pair_context += f"Solution 2:\n{solution_small}\n\n"

    return example_pair_context

def parse_output_all_constraints(problem_spec: str, output: str):
    """
    Parses the output from cvc5 and maps each constraint to whether it failed or not.
    Assumes that the output contains lines indicating the status of each constraint.
    """
    print("\nOutput from cvc5:\n", output)
    constraints = get_constraints(problem_spec)
    
    # Parse variable assignments from the output
    lines = output.strip().split('\n')
    
    # Check if the result is satisfiable
    if lines[0].strip() == 'unsat':
        # If unsat, all constraints pass (no counterexample found)
        return {constraint: True for constraint in constraints}, {}
    
    if lines[0].strip() != 'sat':
        # Handle error cases
        return {constraint: None for constraint in constraints}, {}
    
    # Parse constraint status from lines that start with (((
    constraint_status = {}
    constraint_idx = 0
    
    for line in lines[1:]:
        line = line.strip()
        if line.startswith('(((') and line.endswith('))'):
            # Extract the boolean value (true/false) from the end
            if line.endswith('true))'):
                status = True
            elif line.endswith('false))'):
                status = False
            else:
                status = None
            
            # Map to the corresponding constraint
            if constraint_idx < len(constraints):
                constraint_status[constraints[constraint_idx]] = status
                constraint_idx += 1
    
    # Extract variable assignments from the model
    assignments = {}
    in_model = False
    
    for line in lines:
        line = line.strip()
        if line == '(':
            in_model = True
            continue
        elif line == ')':
            if in_model:
                break
        elif in_model and line.startswith('(define-fun'):
            # Remove the closing parenthesis if it's at the end
            if line.endswith(')'):
                line = line[:-1]
            
            # Extract variable name and value
            parts = line.split()
            if len(parts) >= 5:
                var_name = parts[1]
                # Join everything after the type declaration
                value_part = ' '.join(parts[4:])
                
                # Parse the value
                if value_part == 'true':
                    assignments[var_name] = True
                elif value_part == 'false':
                    assignments[var_name] = False
                elif value_part.startswith('(-') or value_part.startswith('(- '):
                    # Negative number like (- 1)
                    num_str = value_part.replace('(-', '').replace('(- ', '').rstrip(')')
                    try:
                        assignments[var_name] = -int(num_str.strip())
                    except ValueError:
                        assignments[var_name] = value_part
                else:
                    try:
                        assignments[var_name] = int(value_part)
                    except ValueError:
                        assignments[var_name] = value_part
    
    print(f"Parsed constraint status: {constraint_status}")
    print(f"Parsed assignments: {assignments}")
    return constraint_status, assignments

def parse_output_get_counterexample(output: str) -> dict:
    """
    Parses the output from cvc5 to extract the counter example variable assignments.
    Assumes that the output contains lines indicating the variable assignments.
    """
    print("\nOutput from cvc5:\n", output)
    lines = output.strip().split('\n')
    
    # Check if the result is satisfiable
    if lines[0].strip() != 'sat':
        # If not sat, no counterexample
        return {}
    
    # Extract variable assignments from the model
    assignments = {}
    in_model = False
    
    for line in lines:
        line = line.strip()
        if line == '(':
            in_model = True
            continue
        elif line == ')':
            if in_model:
                break
        elif in_model and line.startswith('(define-fun'):
            # Remove the closing parenthesis if it's at the end
            if line.endswith(')'):
                line = line[:-1]
            
            # Extract variable name and value
            parts = line.split()
            if len(parts) >= 5:
                var_name = parts[1]
                # Join everything after the type declaration
                value_part = ' '.join(parts[4:])
                
                # Parse the value
                if value_part == 'true':
                    assignments[var_name] = True
                elif value_part == 'false':
                    assignments[var_name] = False
                elif value_part.startswith('(-') or value_part.startswith('(- '):
                    # Negative number like (- 1)
                    num_str = value_part.replace('(-', '').replace('(- ', '').rstrip(')')
                    try:
                        assignments[var_name] = -int(num_str.strip())
                    except ValueError:
                        assignments[var_name] = value_part
                else:
                    try:
                        assignments[var_name] = int(value_part)
                    except ValueError:
                        assignments[var_name] = value_part
    
    print(f"Parsed assignments (counterexample): {assignments}")
    return assignments

def prepare_context_from_failure(constraint_status, old_solution: str) -> str:
    """
    Prepares a context string from the failure output of cvc5 and the old solution.
    This context can be used to prompt the LLM for a new candidate solution.
    """
    context = f"The previous candidate solution was:\n{old_solution}\n\n"
    
    failing_constraints = [c['name'] for c in constraint_status if c['status'].lower() == "failed"]

    # add failing constraints and counterexamples
    if failing_constraints:
        context += "The following constraints failed Each with their counter examples (a counter example is an assignment of values to the variables that causes the constraint to fail):\n"
        for constraint in failing_constraints:
            context += f"  {constraint}\n"
            # find the corresponding counter example
            for c in constraint_status:
                if constraint == c['name']:
                    counter_example = c.get('counter_example', None)
                    if counter_example:
                        context += f"    Counter example: {counter_example}\n"
        context += "\n"
    
    passing_constraints = [c['name'] for c in constraint_status if c['status'].lower() == "passed"]
    if passing_constraints:
        context += "The following constraints passed:\n"
        for constraint in passing_constraints:
            context += f"  {constraint}\n"
        context += "\n"
    
    context += "Based on the above output, please provide a new candidate solution that satisfy all the constraints.\n"
    context += prepare_format_instruction()
    return context


def prepare_context_from_error(old_solution: str, output: str) -> str:
    """
    Prepares a context string from the error output of cvc5 and the old solution.
    This context can be used to prompt the LLM for a new candidate solution.
    """
    context = f"The candidate solution was:\n{old_solution}\n\n"
    context += "The verification output indicates an error occurred during processing. The error is:\n"
    context += f"{output}\n\n"

    context += "Based on the above error(s), please provide a new candidate solution that avoids the issues.\n"
    prepare_format_instruction()
    return context

def extract_solution_from_response(response: str, VERBOSE: str) -> list[str]:
    """
    Extracts SyGuS solutions from the LLM response.
    If multiple solutions are present, extracts all of them and ensures parentheses are balanced.
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
        print("No wrapped solution found. Attempting to extract solution directly.")

    # solutions = refine_solution_from_wrapped(response, VERBOSE)
    
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

def get_synth_func_name(problem_spec: str) -> str:
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
                print(f"WARNING: Wrong function name: '{found_name}'. Changed to correct name: '{correct_func_name}' in solution.\n")
            else:
                fixed_solutions.append(solution)
        else:
            fixed_solutions.append(solution)
    return fixed_solutions

def prepare_context_for_no_solution(problem_spec: str, solution_history: list[str]) -> str:
    """
    Prepares a context string when no valid solution could be extracted.
    This context can be used to prompt the LLM for a new candidate solution.
    """
    print("No new solution could be extracted from the LLM response.")
    context = "The previous attempts to generate a valid candidate solution have failed.\n"
    if solution_history:
        context += "Here are the previous attempted solutions:\n"
    for idx, sol in enumerate(solution_history):
        context += f"Attempt {idx + 1}:\n{sol}\n\n"
    
    context += "The SyGuS problem specification is as follows:\n"
    context += problem_spec + "\n\n"
    context += "Please provide a new candidate solution that satisfies all the constraints. Don't produce any one of the previous solutions\n"
    context += prepare_format_instruction()
    return context

def check_for_tricks(solution: str) -> bool:
    """
    Checks if the solution is using tricks (i.e., does not start with (define-fun).
    Returns True if tricks are detected, False otherwise.
    """
    return not solution.strip().startswith("(define-fun")

def prepare_context_for_tricks(problem_spec: str, solution: str) -> str:
    """
    Prepares a context string when the LLM response indicates it is using tricks.
    This context can be used to prompt the LLM for a new candidate solution.
    """
    context = f"The candidate solution is:\n{solution}\n\n"
    context += "The solution provided does not adhere to the expected SyGuS format. It appears to be using tricks or is not a valid SyGuS solution.\n"
    context += "The SyGuS problem specification is as follows:\n"
    context += problem_spec + "\n\n"
    context += "Please provide a new candidate solution that satisfies all the constraints and adheres to the SyGuS format.\n"
    context += prepare_format_instruction()
    
    return context

def add_failing_solutions_to_context(context: str, failing_solution: str) -> str:
    """
    Adds the failing solution to the existing context.
    """
    context += f"\nThe previous candidate solution was:\n{failing_solution}\n\n"
    return context

def prepare_format_instruction() -> str:
    """
    Prepares the format instruction for the LLM.
    """
    instruction = ""
    # instruction += "Wrap the entire solution between the markers <<<SOLUTION>>> and <<<END>>> with no extra text or explanation.\n"
    instruction += "Provide only the solution, nothing else. Make sure to use use smt-lib syntax. \
You don't need to include the reasoning or the problem specification in your response.\n\n"
    return instruction

def get_func_signature(text: str, is_sol: bool):
    """
    Extracts function name, argument list, and return type from SyGuS spec or solution.
    If is_sol is True, expects (define-fun ...), else expects (synth-fun ...).
    Returns (func_name, arg_list, return_type).
    arg_list is a list of tuples: [(arg_name, arg_type), ...]
    """
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

def prepare_context_for_argument_mismatch(spec_sig, cand_sig) -> str:
    """
    Prepares a context string when there is an argument mismatch between spec and candidate solution.
    This context can be used to prompt the LLM for a new candidate solution.
    """
    context = f"The number of arguments in your previous solution does not match the specification.\n"
    context += f"Received argument count: {len(cand_sig[1])}\n"
    context += f"Expected arguments and types: {spec_sig[1]}\n"
    context += "Please generate a new solution with the correct number of arguments."
    context += prepare_format_instruction()
    
    return context

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
