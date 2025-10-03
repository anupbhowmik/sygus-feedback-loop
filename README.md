# SyGus Feedback Loop LLM

This repository contains code for a feedback loop system that utilizes Large Language Models (LLMs) to solve Syntax-Guided Synthesis (SyGus) problems. The system iteratively refines its solutions based on feedback from the LLM, aiming to improve the quality and correctness of the synthesized programs.

## Run the program

### Flags

- `-p`: Path to the input SyGus problem file (required).
- `-t` or `--threshold`: Iteration threshold (default: 5).
- `-c` or `--cutoff`: Cutoff time in minutes (default: 30 minutes).
- `-o`: Output file name (optional, if not given, uses a temporary file and won't save the `.smt2` file).
- `-v` or `--verbose`: Enable verbose output for debugging purposes.

### Example

```bash
python llm_loop.py -p <path_to_sygus_file> -o <output_file> -t <threshold> -c <cutoff_time_in_minutes> -v
```

The program will run `threshold` iterations or until the `cutoff` time is reached, whichever comes first.
