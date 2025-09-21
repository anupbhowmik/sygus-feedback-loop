def prepare_context_from_failure(output: str, old_solution: str) -> str:
    """
    Prepares a context string from the failure output of cvc5 and the old solution.
    This context can be used to prompt the LLM for a new candidate solution.
    """
    context = f"The previous candidate solution was:\n{old_solution}\n\n"
    context += "The verification output includes a counter example (an example where the constraints fail). It also contains the exact constraints that fail on the counter example.\nThe output is:\n"
    context += output + "\n\n"
    context += "Based on the above output, please provide a new candidate solution that addresses the issues."
    return context

def prepare_context_from_error(output: str, old_solution: str) -> str:
    """
    Prepares a context string from the error output of cvc5 and the old solution.
    This context can be used to prompt the LLM for a new candidate solution.
    """
    context = f"The previous candidate solution was:\n{old_solution}\n\n"
    context += "The verification output indicates an error occurred during processing. The output is:\n"
    context += output + "\n\n"
    context += "Based on the above error, please provide a new candidate solution that avoids the issues."
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