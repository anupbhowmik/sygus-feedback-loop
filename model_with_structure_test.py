from llm import get_ollama_model, constants, generate_init_prompt, prepare_context_from_failure, prepare_context_from_error, extract_solution_from_response, prepare_context_for_no_solution, prepare_context_for_tricks, check_for_tricks, parse_output_get_counterexample, get_func_signature, prepare_context_for_argument_mismatch, add_return_type_to_solution, fix_synth_func_names, GenerateSolution, Movie


model_name = constants.OLLAMA_LLAMA_4_LATEST
model = get_ollama_model(model_name)
print(f"Using model: {model_name}")

model_with_structure = model.with_structured_output(GenerateSolution)

problem_spec = """
(set-logic LIA)

(synth-fun findIdx ((y1 Int) (y2 Int) (k1 Int)) Int)

(declare-var x1 Int)
(declare-var x2 Int)
(declare-var k Int)
(constraint (=> (< x1 x2) (=> (< k x1) (= (findIdx x1 x2 k) 0))))
(constraint (=> (< x1 x2) (=> (> k x2) (= (findIdx x1 x2 k) 2))))
(constraint (=> (< x1 x2) (=> (and (> k x1) (< k x2)) (= (findIdx x1 x2 k) 1))))

(check-synth)


"""
response = model_with_structure.invoke(f"Generate a solution for the following SyGuS specification:\n{problem_spec}")
print("\n=== LLM Generated Output ===")
print(response)

if not response:
    print("No response received from the model.")
    exit(1)

solution = response.solution
reasoning = response.reasoning

print("Generated Solution:")
print(solution)
print("Reasoning:")
print(reasoning)
