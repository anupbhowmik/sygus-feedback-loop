from checker import check_sygus_solution
from llm import get_ollama_model, constants, generateSyGuSSolution, prepare_context_from_failure, prepare_context_from_error, extract_solution_from_response
import argparse

tools = [generateSyGuSSolution]

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

    model_name = constants.OLLAMA_CODELLAMA_7B
    model = get_ollama_model(model_name)
    print(f"Using model: {model_name}")

    init_prompt = f"""You are a helpful assistant that generates SyGuS solutions based on the given problem specification.
    You will be provided with a SyGuS problem specification. Your task is to generate a valid SyGuS solution that adheres to the constraints and requirements outlined in the specification.
    Ensure that your solution is syntactically correct and logically consistent with the problem statement.\n\n{problem_spec}. Give only the solution, nothing else."""

    prompt = init_prompt
    for iteration in range(args.threshold):
        print(f"--- Iteration {iteration + 1} ---")
        
        try:
            if VERBOSE:
                print(f"Prompt:\n{prompt}\n")
            ai_response = model.invoke(prompt)
        except Exception as e:
            print(f"Error during model invocation: {e}")
            exit(1)

        candidate_solution = extract_solution_from_response(ai_response.content.strip())

        # candidate_solution = args.s
        print(f"Current candidate solution:\n{candidate_solution}")

        output = check_sygus_solution(problem_spec, candidate_solution, iteration, args.o)

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
            prompt = prepare_context_from_failure(output, candidate_solution)
            print("Prompting for a new candidate solution...")
        else:
            print("Error thrown from cvc5.")
            prompt = prepare_context_from_error(output, candidate_solution)
            print("Prompting for a new candidate solution...")
            

            