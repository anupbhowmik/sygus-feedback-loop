from pydantic import BaseModel, Field

class GenerateSMTLIBSolution(BaseModel):
    '''
    Given a SyGuS specification, generate a candidate solution.
    Make sure to only return the solution in SMT-LIB format, without any additional text.
    Produce **exactly one** SMT-LIB solution — a single S-expression of the form:

    (define-fun <name> (<(arg-name arg-type) ...>) Int <y_int>)

    and nothing else (no commentary, no whitespace other than single space separators, no surrounding code blocks).  
    The <name> and argument list must match the synth-fun in the problem. The body must be a valid <y_int> expression constructed **only** from the following grammar and tokens:

    Grammar (strict):
    y_int ::= y_const_int
            | <variable>             ; variable must be exactly one of the declared input argument names
            | (- y_int)
            | (+ y_int y_int)
            | (- y_int y_int)
            | (* y_const_int y_int)
            | (* y_int y_const_int)
            | (div y_int y_const_int)
            | (mod y_int y_const_int)
            | (abs y_int)
            | (ite y_bool y_int y_int)

    y_const_int ::= 0 | 1 | 2 | 3 | ...     ; (only non-negative numerals allowed)
                    ; negative numerals must be written as (- <positive-numeral>)

    y_bool ::= (= y_int y_int)
            | (> y_int y_int)
            | (>= y_int y_int)
            | (< y_int y_int)
            | (<= y_int y_int)

    Strict output rules (must obey ALL):
    1. Output **exactly one S-expression**: the define-fun line as shown above and nothing else.
    2. Use only the tokens and production forms in the grammar. Do not introduce any other functions, keywords, identifiers, or punctuation.
    3. Integer constants in the output body must be non-negative numerals (e.g. 0, 1, 42). For negative constants use unary form: (- 3).
    4. The only identifiers allowed in the body are the function's argument names and the grammar constructs above.
    5. Parentheses must be balanced. Use standard SMT-LIB spacing (single spaces between tokens).
    6. Do not include the original synth-fun, constraints, check-synth, or any additional declarations — output only the define-fun S-expression.
    7. The returned function must type-check in LIA (all subexpressions must respect Int/Bool sorts per grammar).

    Now produce only the define-fun solution for the given synth-fun problem that appears after this instruction.
    '''
    solution: str = Field(..., description="The generated candidate solution in SMT-LIB format and conforming to grammar.")
