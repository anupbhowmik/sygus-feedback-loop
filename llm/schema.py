from pydantic import BaseModel, Field

class GenerateSolution(BaseModel):
    '''
    Given a SyGuS specification, generate a candidate solution.
    Make sure to only return the solution in SMT-LIB format, without any additional text.
    '''
    solution: str = Field(..., description="The generated candidate solution in SMT-LIB format.")
    reasoning: str = Field(..., description="A brief explanation of the solution provided.")


class Movie(BaseModel):
    """A movie with details."""
    title: str = Field(..., description="The title of the movie")
    year: int = Field(..., description="The year the movie was released")
    director: str = Field(..., description="The director of the movie")
    rating: float = Field(..., description="The movie's rating out of 10")
