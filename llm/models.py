from dotenv import load_dotenv
from langchain_openai import ChatOpenAI
from langchain_ollama import ChatOllama
from langchain_huggingface import HuggingFaceEndpoint, ChatHuggingFace
from langchain_groq import ChatGroq
load_dotenv()
import os
from . import constants


API_KEY = os.getenv("OPENAI_API_KEY")
model_openai = ChatOpenAI(
    model=constants.OPENAI_GPT_4O,
    api_key=API_KEY,
)

model_ollama = ChatOllama(
    model=constants.OLLAMA_LLAMA_3_2_3B_INSTRUCT_Q4,
    temperature=0.0,
)

llm_hug = HuggingFaceEndpoint(
    repo_id=constants.HUGGINGFACE_LLAMA_3_2_3B_INSTRUCT,
    task="text-generation",
    max_new_tokens=512,
    do_sample=False,
    repetition_penalty=1.03,
)

model_hug = ChatHuggingFace(llm=llm_hug, verbose=False)

model_groq = ChatGroq(
    model=constants.GROQ_LLAMA_3_3_70B_VERSATILE,
    temperature=0.0,
    max_tokens=None,
    timeout=None,
    max_retries=2,
)

def get_model(model: str):
    if model == constants.OPENAI_GPT_4O:
        return model_openai, model_openai.model_name
    elif model == constants.OLLAMA_LLAMA_3_2_3B_INSTRUCT_Q4:
        return model_ollama, model_ollama.model
    elif model == constants.HUGGINGFACE_LLAMA_3_2_3B_INSTRUCT:
        return model_hug, model_hug.model_id
    elif model == constants.GROQ_LLAMA_3_3_70B_VERSATILE:
        return model_groq, model_groq.model_name
    else:
        raise ValueError(f"Unknown model: {model}")