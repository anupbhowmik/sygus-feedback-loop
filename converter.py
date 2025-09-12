#!/usr/bin/env python
"""
General CVC5 SyGuS to SMT2 converter using command line interface
Works with any SyGuS file and provides flexible conversion options
"""

import subprocess
import re
import os
import sys
import argparse
from pathlib import Path

class SygusToSMT2Converter:
    def __init__(self, cvc5_binary_path="cvc5", timeout=120):
        """
        Initialize converter with path to CVC5 binary
        
        Args:
            cvc5_binary_path: Path to CVC5 executable (default: "cvc5" in PATH)
            timeout: Timeout in seconds for synthesis (default: 120)
        """
        self.cvc5_path = cvc5_binary_path
        self.timeout = timeout
        self._verify_cvc5_installation()
    
    def _verify_cvc5_installation(self):
        """Verify CVC5 is installed and accessible"""
        try:
            result = subprocess.run([self.cvc5_path, "--version"], 
                                  capture_output=True, text=True, timeout=5)
            if result.returncode != 0:
                raise Exception(f"CVC5 not working properly: {result.stderr}")
        except FileNotFoundError:
            raise Exception(f"CVC5 binary not found at: {self.cvc5_path}")
        except Exception as e:
            raise Exception(f"Error verifying CVC5 installation: {e}")
    
    def convert_file(self, sygus_file_path, output_smt2_path=None, include_model=True, 
                    include_constraints=True, add_check_sat=True):
        """
        Convert SyGuS file to SMT2 format
        
        Args:
            sygus_file_path: Path to input .sy file
            output_smt2_path: Path for output .smt2 file (optional)
            include_model: Include synthesized function definitions
            include_constraints: Include original constraints as assertions
            add_check_sat: Add (check-sat) and (get-model) commands
            
        Returns:
            tuple: (success, smt2_content, synthesis_result, error_message)
        """
        if not os.path.exists(sygus_file_path):
            return False, None, None, f"SyGuS file not found: {sygus_file_path}"
        
        try:
            # Run CVC5 on the SyGuS file
            print(f"Running CVC5 on {sygus_file_path}...")
            cmd = [self.cvc5_path, "--lang=sygus", str(sygus_file_path)]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=self.timeout)
            
            synthesis_result = result.stdout.strip()
            
            if result.returncode != 0:
                error_msg = f"CVC5 synthesis failed: {result.stderr}"
                if "timeout" in result.stderr.lower():
                    error_msg += f" (Consider increasing timeout from {self.timeout}s)"
                return False, None, synthesis_result, error_msg
            
            # Generate SMT2 content
            smt2_content = self._generate_smt2_content(
                synthesis_result, sygus_file_path, include_model, 
                include_constraints, add_check_sat
            )
            
            # Save to file if path provided
            if output_smt2_path:
                with open(output_smt2_path, 'w') as f:
                    f.write(smt2_content)
                print(f"SMT2 file saved to: {output_smt2_path}")
            
            return True, smt2_content, synthesis_result, None
            
        except subprocess.TimeoutExpired:
            return False, None, None, f"CVC5 timeout (>{self.timeout}s). Try increasing timeout or simplifying the problem."
        except Exception as e:
            return False, None, None, f"Unexpected error: {str(e)}"
    
    def _generate_smt2_content(self, synthesis_result, original_file, include_model, 
                              include_constraints, add_check_sat):
        """Generate complete SMT2 content from synthesis result and original file"""
        
        smt2_lines = []
        
        # Header
        smt2_lines.extend(self._generate_header(original_file))
        
        # Logic declaration
        logic = self._extract_logic(original_file)
        smt2_lines.append(f"(set-logic {logic})")
        smt2_lines.append("")
        
        # Variable declarations
        var_decls = self._extract_variable_declarations(original_file)
        if var_decls:
            smt2_lines.append("; Variable declarations")
            smt2_lines.extend(var_decls)
            smt2_lines.append("")
        
        # Function declarations (non-synthesis functions)
        func_decls = self._extract_function_declarations(original_file)
        if func_decls:
            smt2_lines.append("; Function declarations")
            smt2_lines.extend(func_decls)
            smt2_lines.append("")
        
        # Synthesized functions
        if include_model:
            model_lines = self._process_synthesis_result(synthesis_result)
            if model_lines:
                smt2_lines.append("; Synthesized functions")
                smt2_lines.extend(model_lines)
                smt2_lines.append("")
        
        # Constraints as assertions
        if include_constraints:
            constraint_lines = self._extract_constraints_as_assertions(original_file)
            if constraint_lines:
                smt2_lines.extend(constraint_lines)
                smt2_lines.append("")
        
        # SMT2 commands
        if add_check_sat:
            smt2_lines.extend([
                "(check-sat)",
                "(get-model)"
            ])
        
        return "\n".join(smt2_lines)
    
    def _generate_header(self, original_file):
        """Generate SMT2 header with metadata"""
        return [
            f"; Generated from SyGuS file: {os.path.basename(original_file)}",
            f"; Conversion tool: CVC5 SyGuS to SMT2 Converter",
            f"; Original file: {os.path.abspath(original_file)}",
            ""
        ]
    
    def _extract_logic(self, sygus_file):
        """Extract logic declaration from SyGuS file"""
        try:
            with open(sygus_file, 'r') as f:
                content = f.read()
            
            logic_match = re.search(r'\(set-logic\s+(\w+)\)', content)
            return logic_match.group(1) if logic_match else "ALL"
        except:
            return "ALL"
    
    def _extract_variable_declarations(self, sygus_file):
        """Extract variable declarations and convert to SMT2 format"""
        declarations = []
        try:
            with open(sygus_file, 'r') as f:
                content = f.read()
            
            # Find declare-var statements
            var_pattern = r'\(declare-var\s+(\w+)\s+([^)]+)\)'
            variables = re.findall(var_pattern, content)
            
            for var_name, var_type in variables:
                declarations.append(f"(declare-const {var_name} {var_type})")
                
        except Exception as e:
            declarations.append(f"; Error extracting variables: {e}")
        
        return declarations
    
    def _extract_function_declarations(self, sygus_file):
        """Extract non-synthesis function declarations"""
        declarations = []
        try:
            with open(sygus_file, 'r') as f:
                content = f.read()
            
            # Find declare-fun statements (not synth-fun)
            func_pattern = r'\(declare-fun\s+(\w+)\s+\(([^)]*)\)\s+([^)]+)\)'
            functions = re.findall(func_pattern, content)
            
            for func_name, params, return_type in functions:
                if params.strip():
                    declarations.append(f"(declare-fun {func_name} ({params}) {return_type})")
                else:
                    declarations.append(f"(declare-const {func_name} {return_type})")
                    
        except Exception as e:
            declarations.append(f"; Error extracting function declarations: {e}")
        
        return declarations
    
    def _process_synthesis_result(self, synthesis_result):
        """Process CVC5 synthesis output and format for SMT2"""
        model_lines = []
        
        if not synthesis_result or "unsat" in synthesis_result.lower():
            model_lines.append("; No synthesis solution found")
            return model_lines
        
        # Handle different output formats
        if synthesis_result.startswith("("):
            # Direct function definitions
            lines = synthesis_result.strip().split('\n')
            for line in lines:
                line = line.strip()
                if line and not line.startswith(';'):
                    model_lines.append(line)
        else:
            # Parse structured output
            define_fun_pattern = r'\(define-fun[^(]*\([^)]*\)[^(]*[^)]*\)'
            matches = re.findall(define_fun_pattern, synthesis_result, re.DOTALL)
            
            if matches:
                model_lines.extend(matches)
            else:
                # Fallback: include raw output as comment
                model_lines.append("; Synthesis result:")
                for line in synthesis_result.split('\n'):
                    if line.strip():
                        model_lines.append(f"; {line.strip()}")
        
        return model_lines
    
    def _extract_constraints_as_assertions(self, sygus_file):
        """Extract constraint statements and convert to SMT2 assertions"""
        assertions = ["; Constraints converted to assertions"]
        
        try:
            with open(sygus_file, 'r') as f:
                content = f.read()
            
            # Find constraint statements with proper parentheses matching
            constraint_matches = []
            lines = content.split('\n')
            
            for line in lines:
                line = line.strip()
                if line.startswith('(constraint'):
                    # Extract the constraint content
                    constraint_content = line[11:].strip()  # Remove '(constraint'
                    if constraint_content.endswith(')'):
                        constraint_content = constraint_content[:-1]  # Remove trailing ')'
                    constraint_matches.append(constraint_content.strip())
            
            for constraint in constraint_matches:
                if constraint:
                    assertions.append(f"(assert {constraint})")
            
            if len(assertions) == 1:  # Only header added
                assertions.append("; No constraints found")
                
        except Exception as e:
            assertions.append(f"; Error extracting constraints: {e}")
        
        return assertions
    
    def convert_directory(self, input_dir, output_dir=None, pattern="*.sy"):
        """
        Convert all SyGuS files in a directory
        
        Args:
            input_dir: Directory containing SyGuS files
            output_dir: Output directory (default: input_dir + "_smt2")
            pattern: File pattern to match (default: "*.sy")
        
        Returns:
            dict: Results for each file {filename: (success, error_message)}
        """
        input_path = Path(input_dir)
        if not input_path.exists():
            raise Exception(f"Input directory not found: {input_dir}")
        
        if output_dir is None:
            output_path = input_path.parent / (input_path.name + "_smt2")
        else:
            output_path = Path(output_dir)
        
        output_path.mkdir(exist_ok=True)
        
        results = {}
        sygus_files = list(input_path.glob(pattern))
        
        if not sygus_files:
            print(f"No files matching pattern '{pattern}' found in {input_dir}")
            return results
        
        print(f"Converting {len(sygus_files)} files from {input_dir} to {output_path}")
        
        for sygus_file in sygus_files:
            output_file = output_path / (sygus_file.stem + ".smt2")
            
            print(f"Converting: {sygus_file.name} -> {output_file.name}")
            success, _, _, error = self.convert_file(sygus_file, output_file)
            
            results[sygus_file.name] = (success, error)
            
            if success:
                print(f"  ✓ Success")
            else:
                print(f"  ✗ Failed: {error}")
        
        return results

def main():
    """Command line interface for the converter"""
    parser = argparse.ArgumentParser(description="Convert SyGuS files to SMT2 format using CVC5")
    
    parser.add_argument("input", help="Input SyGuS file or directory")
    parser.add_argument("-o", "--output", help="Output SMT2 file or directory")
    parser.add_argument("--cvc5-path", default="cvc5", help="Path to CVC5 binary (default: cvc5)")
    parser.add_argument("--timeout", type=int, default=120, help="Timeout in seconds (default: 120)")
    parser.add_argument("--no-constraints", action="store_true", help="Don't include constraints as assertions")
    parser.add_argument("--no-model", action="store_true", help="Don't include synthesized functions")
    parser.add_argument("--no-check-sat", action="store_true", help="Don't add (check-sat) commands")
    parser.add_argument("--pattern", default="*.sy", help="File pattern for directory mode (default: *.sy)")
    
    args = parser.parse_args()
    
    try:
        converter = SygusToSMT2Converter(args.cvc5_path, args.timeout)
        
        input_path = Path(args.input)
        
        if input_path.is_file():
            # Single file conversion
            output_file = args.output or (input_path.stem + ".smt2")
            
            success, smt2_content, synthesis_result, error = converter.convert_file(
                args.input, output_file,
                include_model=not args.no_model,
                include_constraints=not args.no_constraints,
                add_check_sat=not args.no_check_sat
            )
            
            if success:
                print("\n=== Conversion Successful ===")
                if not args.output:
                    print("SMT2 Content:")
                    print("-" * 50)
                    print(smt2_content)
            else:
                print(f"\n=== Conversion Failed ===")
                print(f"Error: {error}")
                sys.exit(1)
                
        elif input_path.is_dir():
            # Directory conversion
            results = converter.convert_directory(args.input, args.output, args.pattern)
            
            successful = sum(1 for success, _ in results.values() if success)
            total = len(results)
            
            print(f"\n=== Batch Conversion Complete ===")
            print(f"Successfully converted: {successful}/{total} files")
            
            if successful < total:
                print("\nFailed conversions:")
                for filename, (success, error) in results.items():
                    if not success:
                        print(f"  {filename}: {error}")
        else:
            print(f"Error: {args.input} is neither a file nor directory")
            sys.exit(1)
            
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()