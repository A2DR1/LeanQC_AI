from langchain_community.document_loaders import TextLoader
from langchain.text_splitter import CharacterTextSplitter
from langchain_openai import ChatOpenAI, OpenAIEmbeddings
from langchain_community.vectorstores import FAISS
from langchain.chains import RetrievalQA
from langchain_ollama import OllamaEmbeddings, OllamaLLM

import os
import sys

# sys.stderr = open(os.devnull, 'w')  # Mute warnings

from dotenv import load_dotenv
import os

# Load .env file
load_dotenv()

# Access your API key safely
# api_key = os.getenv("OPENAI_API_KEY")
# print("API key loaded:", api_key[:8] + "..." if api_key else "Key not found")

model = "ollama"  # "OpenAI" or "Ollama"

Autoformalizing_template = """
You will be given a statement related to quantum computing, expressed in natural (human) language. Your task is to formalize this statement into Lean 4 code, using the definitions, theorems, and notations available in the provided repository as reference and imports.
	•	Ensure that the formalization is syntactically correct Lean 4 code.
	•	If the statement is mathematical (e.g., a definition, identity, or theorem), write it as a theorem or def.
	•	You may assume imports from the repository are available.
	•	If the statement involves standard quantum gates (e.g., Hadamard, CNOT), tensor products, or Dirac notation, represent them using the constructs from the repository.
    •	Ensure the import paths are correct based on the repository structure.
	•	Do not prove the theorem; just state it with := by sorry.

Output format:
A single Lean 4 declaration (e.g., def, theorem) that formalizes the given natural language statement.

natrual language statement: {input}
"""

# approach 1 


def doc_loader(file_path):
    loader = TextLoader(file_path)  # or PDFLoader, UnstructuredLoader, etc.
    documents = loader.load()
    return documents

def docs_loader(file_paths):
    documents = []
    for path in file_paths:
        loader = TextLoader(path)
        docs = loader.load()
        documents.extend(docs)  # Merge all loaded docs into one list
    return documents

def doc_splitter(documents):
    text_splitter = CharacterTextSplitter(chunk_size=500, chunk_overlap=50)
    docs = text_splitter.split_documents(documents)
    return docs

def OpenAI_doc_embedding(docs):
    embeddings = OpenAIEmbeddings()
    vectorstore = FAISS.from_documents(docs, embeddings)
    return vectorstore

def Ollama_doc_embedding(docs):
    embeddings = OllamaEmbeddings(model = "llama2")  # uses Ollama local embedding model
    vectorstore = FAISS.from_documents(docs, embeddings)
    return vectorstore

def setup(file_path):
    documents = doc_loader(file_path)
    docs = doc_splitter(documents)

    llm = None
    
    match model:
        case "ollama":
            vectorstore = Ollama_doc_embedding(docs)
            retriever = vectorstore.as_retriever()
            llm = OllamaLLM(model="llama2:latest", temperature=0)
        case "openAI":
            vectorstore = OpenAI_doc_embedding(docs)
            retriever = vectorstore.as_retriever()
            llm = ChatOpenAI(model_name="gpt-4", temperature=0)

    rag_chain = RetrievalQA.from_chain_type(
        llm=llm,
        retriever=retriever,
        chain_type="stuff"  # can also use "map_reduce", "refine"
    )

    return rag_chain

def read_json_questions(json_file):
    import json
    with open(json_file, 'r') as f:
        data = json.load(f)
    
    questions = [item['statement'] for item in data]
    return questions

def iterate_over_questions(file_path, questions):
    rag_chain = setup(file_path)
    for question in questions:
        query = Autoformalizing_template.format(input=question)  # Format the template with the question
        save_responses_to_file("", "responses.txt")  # Add a newline for separation
        save_responses_to_file(f"Question: {question}", "responses.txt")
        save_responses_to_file("", "responses.txt")
        for i in range(10):
            response = rag_chain.invoke(query)
            save_responses_to_file(response["result"], "responses.txt")
        save_responses_to_file("-" * 50, "responses.txt")

def save_responses_to_file(response, output_file):
    with open(output_file, 'a') as f:
        f.write(response + "\n")

def main():
    print("Setting up RAG approach...")
    file_path = "sample.txt"  # Update with your document path
    # file_path = "repo.txt"  # Update with your document path
    rag_chain = setup(file_path)

    question = "Measuring a state |\psi\rangle = \sum_i \alpha_i |i\rangle in an orthonormal basis \{|i\rangle\} collapses it to |i\rangle with probability |\alpha_i|^2."
    
    query = Autoformalizing_template.format(input=question)  # Format the template with the question
    response = rag_chain.invoke(query)
    print("Response:", response["result"])


    # questions = read_json_questions("theoremlist.json")
    # print(f"Total questions: {len(questions)}")
    # file_path = "repo.txt"  # Update with your document path
    # iterate_over_questions(file_path, questions)

if __name__ == "__main__":
    main()