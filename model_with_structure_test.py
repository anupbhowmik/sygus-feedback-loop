from llm import get_ollama_model, constants, GenerateSolution

model_name = constants.OLLAMA_GPT_OSS_20B
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
