from pydantic import BaseModel, Field

class Solution(BaseModel):
    '''
    Given a SyGuS specification, generate a candidate solution.
    Make sure to only return the solution in SMT-LIB format, without any additional text.
    '''
    solution: str = Field(..., description="The generated candidate solution in SMT-LIB format.")
    reasoning: str = Field(..., description="A brief explanation of the solution provided.")