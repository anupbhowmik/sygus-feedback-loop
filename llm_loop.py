from checker import check_sygus_solution
from convert import convert_sygus_to_smt2
from llm import get_ollama_model, constants, prepare_context_from_failure, prepare_context_from_error, extract_solution_from_response, pick_best_solution, prepare_context_for_no_solution, prepare_context_for_tricks, check_for_tricks, example_pair_context
import argparse

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="Check SyGuS solution using cvc5.")
    parser.add_argument("-p", required=True, help="Input SyGuS problem file")
    parser.add_argument("-t", "--threshold", type=int, default=5, help="iteration threshold (default: 5)")
    parser.add_argument("-o", "-o", help="Output file name (optional, if not given, use temp file)", default=None)
    parser.add_argument("-v", "--verbose", action="store_true", help="Enable verbose output")
    # parser.add_argument("-s", required=True, help="Candidate solution as a string")

    args = parser.parse_args()
    VERBOSE = args.verbose

    print(f"Reading problem file: {args.p}")
    with open(args.p, "r") as f:
        problem_spec = f.read()

    # candidate_solution = args.s
    # output = check_sygus_solution(problem_spec, candidate_solution, 0, args.o)
    # print(f"cvc5 output:\n{output}")
    
    model_name = constants.OLLAMA_LLAMA_4_17B
    model = get_ollama_model(model_name)
    print(f"Using model: {model_name}")

    init_prompt = f"""You are a helpful assistant that generates SyGuS solutions based on the given problem specification."""
    init_prompt += example_pair_context()
    init_prompt += f"You will be provided with a SyGuS problem specification. \
Your task is to generate a valid SyGuS solution that adheres to the constraints and requirements outlined in the specification.\
Ensure that your solution is syntactically correct and logically consistent with the problem statement.\n\n{problem_spec}. Provide only the solution, nothing else. \
You don't need to include the reasoning or the problem specification in your response."


    prompt = init_prompt
    solution_history = []
    conversation_history = []  # Track full prompt-response history
    
    for iteration in range(args.threshold):
        print(f"--- Iteration {iteration + 1} ---")
        
        try:
            if VERBOSE:
                print(f"\n=================\nPrompt:\n{prompt}\n=================\n")
            ai_response = model.invoke(prompt)
            if VERBOSE:
                print(f"\n=================\nLLM Response:\n{ai_response.content.strip()}\n=================\n")
        except Exception as e:
            print(f"Error during model invocation: {e}")
            exit(1)
        
        # Store the current prompt-response pair
        conversation_history.append({
            "iteration": iteration + 1,
            "prompt": prompt,
            "response": ai_response.content.strip()
        })

        proposed_solutions = extract_solution_from_response(ai_response.content.strip())
        # candidate_solution = args.s
        candidate_solution = pick_best_solution(proposed_solutions, solution_history)
        if VERBOSE:
            print(f"Proposed solutions:\n{proposed_solutions}\n")
            print(f"Selected candidate solution:\n{candidate_solution}\n")

        if not candidate_solution:
            prompt = prepare_context_for_no_solution(problem_spec, solution_history)
            # Add conversation history to prompt
            prompt += f"\n\nPrevious conversation history:\n"
            for conv in conversation_history[-3:]:  # Include last 3 conversations to avoid too long prompts
                prompt += f"Iteration {conv['iteration']} - Response: {conv['response']}\n"
            continue
        if check_for_tricks(candidate_solution):
            print("Detected trick in the candidate solution. Prompting for a new candidate solution")
            prompt = prepare_context_for_tricks(problem_spec, solution_history)
            # Add conversation history to prompt
            prompt += f"\n\nPrevious conversation history:\n"
            for conv in conversation_history[-3:]:  # Include last 3 conversations
                prompt += f"Iteration {conv['iteration']} - Response: {conv['response']}\n"
            continue
        

        solution_history.append(candidate_solution)

        sm2Spec = convert_sygus_to_smt2(problem_spec, candidate_solution)

        output = check_sygus_solution(sm2Spec, iteration, args.o)

        if "unsat" in output.lower():
            print("The candidate solution is correct (unsat). Exiting.")
            # save the correct solution to a file
            save_file = args.p + "_solution.txt"
            with open(save_file, "w") as f:
                f.write(candidate_solution)
            print(f"Correct solution saved to {save_file}")
            break
        elif "sat" in output.lower():
            print("The candidate solution is incorrect (sat).")
            # generate a new candidate solution
            prompt = prepare_context_from_failure(problem_spec, output, candidate_solution)
            print("Prompting for a new candidate solution")
        else:
            print("Error thrown from cvc5.")
            prompt = prepare_context_from_error(output, candidate_solution)
            print("Prompting for a new candidate solution")
        
        prompt += f"\nHere are the previously failed solutions:\n{solution_history}\n"
        
        # Add conversation history context to the prompt
        prompt += f"\nPrevious conversation history:\n"
        for conv in conversation_history[-3:]:  # Include last 3 conversations to manage prompt length
            prompt += f"Iteration {conv['iteration']}:\nYour previous response: {conv['response']}\n\n"