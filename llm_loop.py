from checker import check_sygus_solution
from convert import convert_sygus_to_smt2_per_constraint
from llm import get_ollama_model, constants, prepare_context_from_failure, prepare_context_from_error, extract_solution_from_response, pick_best_solution, prepare_context_for_no_solution, prepare_context_for_tricks, check_for_tricks, example_pair_context, parse_output_get_counterexample
import argparse
import time
import csv
import os
from pathlib import Path

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="Check SyGuS solution using cvc5.")
    parser.add_argument("-p", required=True, help="Input SyGuS problem file")
    parser.add_argument("-t", "--threshold", type=int, default=5, help="iteration threshold (default: 5)")
    parser.add_argument("-c", "--cutoff", type=int, default=30, help="Cutoff time in minutes (default: 30 minutes)")
    parser.add_argument("-o", "-o", help="Output file name (optional, if not given, use temp file)", default=None)
    parser.add_argument("-v", "--verbose", action="store_true", help="Enable verbose output")
    # parser.add_argument("-s", required=True, help="Candidate solution as a string")

    args = parser.parse_args()
    VERBOSE = args.verbose
    CUTOFF_TIME = args.cutoff * 60
    ITERATION_THRESHOLD = args.threshold

    print(f"Reading problem file: {args.p}")
    with open(args.p, "r") as f:
        problem_spec = f.read()

    # candidate_solution = args.s
    # output = check_sygus_solution(problem_spec, candidate_solution, 0, args.o)
    # print(f"cvc5 output:\n{output}")
    
    model_name = constants.OLLAMA_CODELLAMA_7B
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

    global_start_time = time.time()
    success = False
    final_iteration = 0
    termination_reason = "max_iterations"
    
    for iteration in range(ITERATION_THRESHOLD):
        final_iteration = iteration + 1

        current_time = time.time()
        if current_time - global_start_time >= CUTOFF_TIME:
            print(f"CUTOFF_TIME of {CUTOFF_TIME} seconds ({CUTOFF_TIME // 60} minutes) reached. Terminating.")
            termination_reason = "timeout"
            break

        print(f"--- Iteration {iteration + 1} ---")

        iteration_start_time = time.time()
        
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

        smt2SpecList = convert_sygus_to_smt2_per_constraint(problem_spec, candidate_solution)

        constraint_status = []
        counter_examples = []
        output_list = []
        all_passed = True
        
        for idx, smt2_spec in enumerate(smt2SpecList):
            output = check_sygus_solution(smt2_spec, iteration, args.o)
            output_list.append(output)
            
            if "unsat" in output.lower():
                constraint_status.append((idx, "passed"))
                if VERBOSE:
                    print(f"Constraint {idx} passed (unsat).")
            elif "sat" in output.lower():
                constraint_status.append((idx, "failed"))
                all_passed = False
                if VERBOSE:
                    print(f"Constraint {idx} failed (sat).")
                counter_example = parse_output_get_counterexample(output)
                counter_examples.append((idx, counter_example))
            else:
                constraint_status.append((idx, "error"))
                all_passed = False
                if VERBOSE:
                    print(f"Constraint {idx} returned an error.")

        if VERBOSE:
            print(f"Constraint status: {constraint_status}")
            print(f"Counter examples: {counter_examples}")

        if all_passed:
            print("The candidate solution is correct (unsat for all constraints). Exiting.")
            success = True
            termination_reason = "solved"
            # save the correct solution to a file
            # save_file = args.p + "_solution.txt"
            # with open(save_file, "w") as f:
            #     f.write(candidate_solution)
            # print(f"Correct solution saved to {save_file}")
            break
        elif any(status == "error" for idx, status in constraint_status):
            print("Error thrown from cvc5.")

            prompt = prepare_context_from_error(problem_spec, output_list, constraint_status, candidate_solution)
            print("Prompting for a new candidate solution")
        else:
            print("The candidate solution is incorrect (sat for some constraints).")
            # generate a new candidate solution
            prompt = prepare_context_from_failure(problem_spec, output_list, constraint_status, counter_examples, candidate_solution)
            print("Prompting for a new candidate solution")
        
        prompt += f"\nHere are the previously failed solutions:\n{solution_history}\n"
        
        # Add conversation history context to the prompt
        prompt += f"\nPrevious conversation history:\n"
        for conv in conversation_history[-3:]:  # Include last 3 conversations to manage prompt length
            prompt += f"Iteration {conv['iteration']}:\nYour previous response: {conv['response']}\n\n"

        iteration_end_time = time.time()
        print(f"Iteration {iteration + 1} completed in {iteration_end_time - iteration_start_time:.3f} seconds.\n")
    
    global_end_time = time.time()
    total_time = global_end_time - global_start_time
    print(f"Total time elapsed: {total_time:.3f} seconds.")

    # Write results to CSV
    input_filename = Path(args.p).name
    csv_filename = "logs/summary.csv"
    
    csv_data = {
        'input_file': input_filename,
        'total_time_seconds': round(total_time, 3),
        'success': "Success" if success else "Failure",
        'num_iterations': final_iteration,
        'model': model_name,
        'termination_reason': termination_reason,
        'timestamp': time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(global_start_time)),
        'solution': candidate_solution if success else ""
    }

    # Check if CSV file exists to determine if we need to write headers
    csv_exists = os.path.exists(csv_filename)
    
    with open(csv_filename, 'a', newline='') as csvfile:
        fieldnames = ['input_file', 'total_time_seconds', 'success', 'num_iterations', 'model', 'termination_reason', 'timestamp', 'solution']
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        
        # Write header if file is new
        if not csv_exists:
            writer.writeheader()
        
        writer.writerow(csv_data)
    
    print(f"Results appended to {csv_filename}")