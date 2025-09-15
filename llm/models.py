from dotenv import load_dotenv
from langchain_openai import ChatOpenAI
from langchain_ollama import ChatOllama
from langchain_huggingface import HuggingFaceEndpoint, ChatHuggingFace
from langchain_groq import ChatGroq
load_dotenv()
import os

API_KEY = os.getenv("OPENAI_API_KEY")

def get_openai_model(model_name: str, api_key: str = API_KEY):
    return ChatOpenAI(
        model=model_name,
        api_key=api_key,
    )

def get_ollama_model(model_name: str, temperature: float = 0.0):
    return ChatOllama(
        model=model_name,
        temperature=temperature,
    )

def get_huggingface_model(model_name: str):
    llm_hug = HuggingFaceEndpoint(
        repo_id=model_name,
        task="text-generation",
        max_new_tokens=512,
        do_sample=False,
        repetition_penalty=1.03,
    )
    return ChatHuggingFace(llm=llm_hug, verbose=False)

def get_groq_model(model_name: str, temperature: float = 0.0):
    return ChatGroq(
        model=model_name,
        temperature=temperature,
        max_tokens=None,
        timeout=None,
        max_retries=2,
    )