from checker import check_sygus_solution
from llm import get_model, constants, generateSyGuSSolution
import argparse

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="Check SyGuS solution using cvc5.")
    parser.add_argument("--p", required=True, help="Input SyGuS problem file")
    parser.add_argument("--s", required=True, help="Candidate solution as a string")
    parser.add_argument("--o", "-o", help="Output file name (optional, if not given, use temp file)", default=None)

    args = parser.parse_args()

    tools = [generateSyGuSSolution]

    model_name = constants.OPENAI_GPT_4O
    model, model_name = get_model(model_name)
    print(f"Using model: {model_name}")

    output = check_sygus_solution(args.p, args.s, args.o)
    print(f"Output: {output}")