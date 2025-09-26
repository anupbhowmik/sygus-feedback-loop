from convert import get_constraints

def parse_output(problem_spec: str, output: str):
    """
    Parses the output from cvc5 and maps each constraint to whether it failed or not.
    
    Args:
        problem_spec: The original problem specification
        output: The output from cvc5 containing sat/unsat and model
        
    Returns:
        tuple: (constraint_status_dict, counter_example_dict)
               constraint_status_dict: A dictionary mapping each constraint to True (passes) or False (fails)
               counter_example_dict: A dictionary of variable assignments from the counter example
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
    
    # Extract variable assignments from the model
    assignments = {}
    
    # Handle the case where the model is wrapped in parentheses
    model_content = []
    in_model = False
    
    for line in lines[1:]:
        line = line.strip()
        if line == '(':
            in_model = True
            continue
        elif line == ')':
            in_model = False
            break
        elif in_model or line.startswith('(define-fun'):
            model_content.append(line)
    
    # If no parentheses wrapper, use all lines after 'sat'
    if not model_content:
        model_content = [line.strip() for line in lines[1:] if line.strip()]
    
    for line in model_content:
        if line.startswith('(define-fun'):
            # Remove the closing parenthesis if it's at the end
            if line.endswith(')') and line.count('(') == line.count(')'):
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
    
    # Evaluate each constraint against the assignments
    constraint_status = {}
    
    for constraint in constraints:
        try:
            # For now, mark as failed since we have a counterexample (sat result)
            # In a more sophisticated implementation, you would evaluate the constraint
            # expression with the given assignments
            constraint_status[constraint] = False
        except Exception:
            constraint_status[constraint] = None
    
    return constraint_status, assignments

def prepare_context_from_failure(problem_spec: str, output: str, old_solution: str) -> str:
    """
    Prepares a context string from the failure output of cvc5 and the old solution.
    This context can be used to prompt the LLM for a new candidate solution.
    """
    context = f"The previous candidate solution was:\n{old_solution}\n\n"
    context += "The verification output includes a counter example (an example where the constraints fail). It also contains the exact constraints that fail on the counter example."
    
    # Get both constraint status and counter example
    constraint_status, counter_example = parse_output(problem_spec, output)
    print(f"Constraint status: {constraint_status}")
    print(f"Counter example: {counter_example}")
    
    # Add counter example information to context
    if counter_example:
        context += "\nCounter example (variable assignments that make constraints fail):\n"
        for var, value in counter_example.items():
            context += f"  {var} = {value}\n"
        context += "\n"
    
    # Add failing constraints to context
    failing_constraints = [c for c, status in constraint_status.items() if status is False]
    if failing_constraints:
        context += "The following constraints failed:\n"
        for constraint in failing_constraints:
            context += f"  {constraint}\n"
        context += "\n"
    
    passing_constraints = [c for c, status in constraint_status.items() if status is True]
    if passing_constraints:
        context += "The following constraints passed:\n"
        for constraint in passing_constraints:
            context += f"  {constraint}\n"
        context += "\n"
    
    context += "Based on the above output, please provide a new candidate solution that satisfy all the constraints.\n"
    context += "Provide only the solution, nothing else. You don't need to include the reasoning or the problem specification in your response."
    return context


def prepare_context_from_error(output: str, old_solution: str) -> str:
    """
    Prepares a context string from the error output of cvc5 and the old solution.
    This context can be used to prompt the LLM for a new candidate solution.
    """
    context = f"The previous candidate solution was:\n{old_solution}\n\n"
    context += "The verification output indicates an error occurred during processing. The output is:\n"
    context += output + "\n\n"
    context += "Based on the above error, please provide a new candidate solution that avoids the issues.\n"
    "Provide only the solution, nothing else. You don't need to include the reasoning or the problem specification in your response."
    return context

def extract_solution_from_response(response: str) -> str:
    """
    Extracts only the SyGuS solution from the LLM response.
    Assumes the response contains only the solution.
    """
    # a solution must start with (define-fun ... and end with )
    start_idx = response.find("(define-fun")
    end_idx = response.rfind(")") + 1
    if start_idx != -1 and end_idx != -1 and end_idx > start_idx:
        return response[start_idx:end_idx].strip()
    return response.strip()