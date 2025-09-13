from checker.utils import check_sygus_solution
import argparse

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="Check SyGuS solution using cvc5.")
    parser.add_argument("--p", required=True, help="Input SyGuS problem file")
    parser.add_argument("--s", required=True, help="Candidate solution as a string")
    parser.add_argument("--o", "-o", help="Output file name (optional, if not given, use temp file)", default=None)

    args = parser.parse_args()

    output = check_sygus_solution(args.p, args.s, args.o)
    print(f"Output: {output}")