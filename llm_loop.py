from checker import check_sygus_solution
from llm import get_ollama_model, constants, generateSyGuSSolution
import argparse

tools = [generateSyGuSSolution]

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="Check SyGuS solution using cvc5.")
    parser.add_argument("-p", required=True, help="Input SyGuS problem file")
    parser.add_argument("-s", required=True, help="Candidate solution as a string")
    parser.add_argument("-o", "-o", help="Output file name (optional, if not given, use temp file)", default=None)

    args = parser.parse_args()

    print(f"Reading problem file: {args.p}")
    with open(args.p, "r") as f:
        problem_spec = f.read()

    model_name = constants.OLLAMA_CODELLAMA_7B
    model = get_ollama_model(model_name)
    print(f"Using model: {model_name}")

    init_prompt = f"""You are a helpful assistant that generates SyGuS solutions based on the given problem specification.
    You will be provided with a SyGuS problem specification. Your task is to generate a valid SyGuS solution that adheres to the constraints and requirements outlined in the specification.
    Ensure that your solution is syntactically correct and logically consistent with the problem statement.\n\n{problem_spec}"""

    try:
        ai_response = model.invoke(init_prompt)
    except Exception as e:
        print(f"Error during model invocation: {e}")
        exit(1)
    print(f"Model response: {ai_response.content}")

    output = check_sygus_solution(problem_spec, args.s, args.o)
    print(f"Output: {output}")