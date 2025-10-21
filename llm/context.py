from convert import get_constraints

def example_pair_context():
    """
    Returns an example pair of (problem_spec, solution).
    """
    problem_spec_diff = """(set-logic LIA)

(synth-fun f ((x Int) (y Int)) Int)

(declare-var x Int)
(declare-var y Int)
(constraint (= (f x y) (f y x)))
(constraint (and (>= x (f x y)) (>= y (f x y))))

(check-synth)
"""
    solution_diff = """(
(define-fun f ((x Int) (y Int)) Int (ite (<= y x) y x))
)
"""

    problem_spec_array_search = """
(set-logic LIA)

(synth-fun findIdx ((y1 Int) (y2 Int) (y3 Int) (k1 Int)) Int)

(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var k Int)
(constraint (=> (and (< x1 x2) (< x2 x3)) (=> (< k x1) (= (findIdx x1 x2 x3 k) 0))))
(constraint (=> (and (< x1 x2) (< x2 x3)) (=> (> k x3) (= (findIdx x1 x2 x3 k) 3))))
(constraint (=> (and (< x1 x2) (< x2 x3)) (=> (and (> k x1) (< k x2)) (= (findIdx x1 x2 x3 k) 1))))
(constraint (=> (and (< x1 x2) (< x2 x3)) (=> (and (> k x2) (< k x3)) (= (findIdx x1 x2 x3 k) 2))))

(check-synth)
"""
    solution_array_search = """(
(define-fun findIdx ((y1 Int) (y2 Int) (y3 Int) (k1 Int)) Int (let ((_let_1 (* (- 1) k1))) (let ((_let_2 (+ y1 _let_1))) (let ((_let_3 (>= _let_2 1))) (let ((_let_4 (not _let_3))) (let ((_let_5 (+ y3 _let_1))) (let ((_let_6 (>= _let_5 1))) (let ((_let_7 (+ y2 _let_1))) (let ((_let_8 (>= _let_7 0))) (let ((_let_9 (or _let_8 (not _let_6)))) (let ((_let_10 (>= _let_5 0))) (let ((_let_11 (>= _let_7 1))) (let ((_let_12 (>= _let_2 0))) (let ((_let_13 (or _let_12 (not _let_11)))) (ite (and (not (>= (+ y1 (* (- 1) y2)) 0)) (not (>= (+ y2 (* (- 1) y3)) 0)) (or _let_3 (not _let_10) (and (not _let_8) _let_6) (and (not _let_12) _let_11))) (ite (and _let_10 _let_9 _let_13) 0 (ite (and _let_10 _let_13 _let_4) 2 (ite (and _let_10 _let_9 _let_4) 1 3))) (- 1))))))))))))))))
)
"""
    example_pair_context = f"Here are some examples of SyGuS problem specifications and their corresponding solutions as context, you don't need to solve them, they are given just as examples.\n\n"
    example_pair_context += f"Problem Specification 1:\n{problem_spec_diff}\n"
    example_pair_context += f"Solution 1:\n{solution_diff}\n\n"
    example_pair_context += f"Problem Specification 2:\n{problem_spec_array_search}\n"
    example_pair_context += f"Solution 2:\n{solution_array_search}\n\n"

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

def prepare_context_from_failure(problem_spec: str, output_list: list[str], constraint_status: list[str], counter_examples: list[str], old_solution: str) -> str:
    """
    Prepares a context string from the failure output of cvc5 and the old solution.
    This context can be used to prompt the LLM for a new candidate solution.
    """
    context = f"The previous candidate solution was:\n{old_solution}\n\n"
    context += "The verification output includes a counter example (an example where the constraints fail). It also contains the exact constraints that fail on the counter example."
    
    print(f"Constraint status: {constraint_status}")
    print(f"Counter examples: {counter_examples}")
    
    # Add failing constraints to context
    # constraint_status: "passed", "failed", "error"
    failing_constraints = [c for c, status in constraint_status.items() if status.lower() == "failed"]
    if failing_constraints:
        context += "The following constraints failed:\n"
        for constraint in failing_constraints:
            context += f"  {constraint}\n"
            # find the corresponding counter example
            for idx, ce in counter_examples:
                if constraint == failing_constraints[idx]:
                    context += f"    Counter example: {ce}\n"
        context += "\n"
    
    passing_constraints = [c for c, status in constraint_status.items() if status.lower() == "passed"]
    if passing_constraints:
        context += "The following constraints passed:\n"
        for constraint in passing_constraints:
            context += f"  {constraint}\n"
        context += "\n"
    
    context += "Based on the above output, please provide a new candidate solution that satisfy all the constraints.\n"
    context += "Provide only the solution, nothing else. You don't need to include the reasoning or the problem specification in your response."
    return context


def prepare_context_from_error(problem_spec: str, output_list: list[str], constraint_status: list[str], old_solution: str) -> str:
    """
    Prepares a context string from the error output of cvc5 and the old solution.
    This context can be used to prompt the LLM for a new candidate solution.
    """
    context = f"The previous candidate solution was:\n{old_solution}\n\n"
    context += "The verification output indicates an error occurred during processing. The output is:\n"

    # map the error outputs to their constraints
    constraints = get_constraints(problem_spec)
    for idx, status in constraint_status:
        if status == "error":
            context += f"Constraint that caused error:\n  {constraints[idx]}\n"
            context += f"Error output:\n{output_list[idx]}\n\n"

    context += "Based on the above error(s), please provide a new candidate solution that avoids the issues.\n"
    "Provide only the solution, nothing else. You don't need to include the reasoning or the problem specification in your response."
    return context

def extract_solution_from_response(response: str) -> list[str]:
    """
    Extracts SyGuS solutions from the LLM response.
    If multiple solutions are present, extracts all of them.
    Returns a single string containing all solutions.
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
        
        for i in range(start_idx, len(response)):
            if response[i] == '(':
                paren_count += 1
            elif response[i] == ')':
                paren_count -= 1
                if paren_count == 0:
                    end_idx = i + 1
                    break
        
        if paren_count == 0:  # Found a complete solution
            solution = response[start_idx:end_idx].strip()
            solutions.append(solution)
            start_pos = end_idx
        else:
            # Incomplete solution, break
            break
    
    return solutions

def pick_best_solution(solutions: list[str], solution_history: list[str]) -> str:
    """
    Picks the best solution from a list of candidate solutions.
    Currently, it just returns the first solution that is not previously seen.
    """
    for solution in solutions:
        if solution not in solution_history:
            return solution
    # If all solutions have been seen, return None
    return None

def prepare_context_for_no_solution(problem_spec: str, solution_history: list[str]) -> str:
    """
    Prepares a context string when no valid solution could be extracted.
    This context can be used to prompt the LLM for a new candidate solution.
    """
    print("No new solution could be extracted from the LLM response.")
    context = "The previous attempts to generate a valid candidate solution have failed. The history of attempted solutions is as follows:\n"
    for idx, sol in enumerate(solution_history):
        context += f"Attempt {idx + 1}:\n{sol}\n\n"
    
    context += "The SyGuS problem specification is as follows:\n"
    context += problem_spec + "\n\n"
    context += "Please provide a new candidate solution that satisfies all the constraints. Don't produce any one of the previous solutions\n"
    context += "Provide only the solution, nothing else. You don't need to include the reasoning or the problem specification in your response."
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
    context += "Provide only the solution, nothing else. You don't need to include the reasoning or the problem specification in your response."
    
    return context

def add_failing_solutions_to_context(context: str, failing_solution: str) -> str:
    """
    Adds the failing solution to the existing context.
    """
    context += f"\nThe previous candidate solution was:\n{failing_solution}\n\n"
    return context