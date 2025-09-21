# SyGus Feedback Loop LLM

This repository contains code for a feedback loop system that utilizes Large Language Models (LLMs) to solve Syntax-Guided Synthesis (SyGus) problems. The system iteratively refines its solutions based on feedback from the LLM, aiming to improve the quality and correctness of the synthesized programs.

## Run the program

To run the program, use the following command:

```bash
python llm_loop.py -p <path_to_sygus_file> -t -o <output_file>
```

Replace `<path_to_sygus_file>` with the path to your SyGus problem file and `<output_file>` with the desired output file name. `-o` is optional; if not provided, the program will generate a temporary file and solve the problem without saving the `.smt2` file. The `-t` flag sets the iteration threshold (default is 5).
Add the `-v` flag to enable verbose output for debugging purposes.
