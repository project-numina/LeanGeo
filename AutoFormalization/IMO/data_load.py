from huggingface_hub import login
login(token="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")
from huggingface_hub import HfApi

api = HfApi()
api.upload_file(
    path_or_fileobj="data/GeometryLeanBench.parquet",  # 本地 JSON 文件路径
    path_in_repo="data/GeometryLeanBench.parquet",  # 在存储库中的路径
    repo_id="AI-MO/GeometryLeanBench",  # 存储库名称
    repo_type="dataset",  # 指定存储库类型为数据集
)