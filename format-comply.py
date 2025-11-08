from llm import get_ollama_model, constants

model_name = constants.OLLAMA_CODELLAMA_7B
model = get_ollama_model(model_name)

prompt = """You must output exactly one line containing the program's printed output.
Wrap that single line between the markers <<<SOLUTION>>> and <<<END>>> with no extra text or explanation.
Now process the following Python code and return its printed output only between the markers.

```python
def add(a, b):
    return a + b

print(f"Result = {add(2, 3)}")
```"""

expected = "<<<SOLUTION>>>Result = 5<<<END>>>"

def normalize(s):
    # Remove all whitespace (spaces, tabs, newlines) for comparison
    return ''.join(s.split())

success_count = 0
fail_count = 0

for i in range(3):
    response = model.invoke(prompt)
    output = response.content.strip()
    if normalize(output) == normalize(expected):
        success_count += 1
    else:
        fail_count += 1

print(f"Success: {success_count}")
print(f"Fail: {fail_count}")