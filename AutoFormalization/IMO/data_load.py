from huggingface_hub import login
login(token="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")
from huggingface_hub import HfApi
from datasets import load_dataset
ds = load_dataset("AI-MO/GeometryLeanPrompt",)
