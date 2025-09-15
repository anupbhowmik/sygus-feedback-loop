from pydantic import BaseModel, Field

class generateSyGuSSolution(BaseModel):
    '''
    Given a SyGuS specification, generate a candidate solution.
    Make sure to only return the solution in SMT-LIB format, without any additional text.
    '''
    solution: str = Field(..., description="The generated candidate solution in SMT-LIB format.")
