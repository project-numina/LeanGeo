
from huggingface_hub import login
login(token="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")
from datasets import load_dataset
ds = load_dataset("AI-MO/rl-promptset-v4.1-metrics",)
ds['train'].to_json('data/trainAIMOmetrics.json', orient='records', lines=True)
ds['test'].to_json('data/testAIMOmetrics.json', orient='records', lines=True)