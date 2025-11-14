def get_func_signature(text: str, is_sol: bool):
    """
    Extracts function name, argument list, and return type from SyGuS spec or solution.
    If is_sol is True, expects (define-fun ...), else expects (synth-fun ...).
    Returns (func_name, arg_list, return_type).
    arg_list is a list of tuples: [(arg_name, arg_type), ...]
    """
    import re
    if is_sol:
        # (define-fun funcName ((argName argType) ...) returnType ...)
        pattern = r'\(define-fun\s+([^\s\(\)]+)\s+\((.*?)\)\s+([^\s\(\)]+)'
    else:
        # (synth-fun funcName ((argName argType) ...) returnType)
        pattern = r'\(synth-fun\s+([^\s\(\)]+)\s+\((.*?)\)\s+([^\s\(\)]+)\s*\)'
    match = re.search(pattern, text, re.DOTALL)
    if not match:
        return "", [], ""
    func_name = match.group(1)
    args_str = match.group(2)
    return_type = match.group(3)
    arg_list = []
    for arg_match in re.finditer(r'\(([^\s\(\)]+)\s+([^\s\(\)]+)\)', args_str):
        arg_list.append((arg_match.group(1), arg_match.group(2)))
    return func_name, arg_list, return_type

spec = """
(synth-fun findIdx ((x0 Int) (x1 Int) (x2 Int) (x3 Int) (x4 Int) (x5 Int) (x6 Int) (x7 Int) (x8 Int) (x9 Int) (x10 Int) (x11 Int) (x12 Int) (x13 Int) (x14 Int) (x15 Int) (k Int)) Int)"""
print("func signature from spec:")
print(get_func_signature(spec, is_sol=False))

solution = """
;solution
(define-fun findIdx ((x1 Int) (x2 Int) (x3 Int) (x4 Int) (x5 Int) (x6 Int) (x7 Int) (x8 Int) (x9 Int) (x10 Int) (x11 Int) (x12 Int) (x13 Int) (x14 Int) (x15 Int) (k Int))
  (ite (<= k x1) 0
    (ite (<= k x2) 1
      (ite (<= k x3) 2
        (ite (<= k x4) 3
          (ite (<= k x5) 4
            (ite (<= k x6) 5
              (ite (<= k x7) 7
                (ite (<= k x8) 8
                  (ite (<= k x9) 9
                    (ite (<= k x10) 10
                      (ite (<= k x11) 11
                        (ite (<= k x12) 12
                          (ite (<= k x13) 13
                            (ite (<= k x14) 14
                              (ite (<= k x15) 15 15))))))))))))))))
"""
print("func signature from solution:")
print(get_func_signature(solution, is_sol=True))

