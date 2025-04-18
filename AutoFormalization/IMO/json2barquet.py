import pandas as pd
import pyarrow as pa
import pyarrow.parquet as pq
import json
# 读取 JSONL 文件
def read_jsonl_file(file_path):
  data = []
  with open(file_path, 'r', encoding='utf-8') as file:
      for line in file:
          try:
              data.append(json.loads(line))
          except:
              print(line)
              1/0
  return data

# 保存为 Parquet 文件
def save_parquet(file_path, data):
  if isinstance(data, list):
      data = pd.DataFrame(data)
  if not isinstance(data, pd.DataFrame):
      raise ValueError("data must be a pandas DataFrame or a list of lists")
  pq.write_table(pa.Table.from_pandas(data), file_path)
  print(f'Save {file_path} is ok!')

# 示例
file_path = 'data/GeometryLeantest.jsonl'
save_path = 'data/GeometryLeanBench.parquet'
data = read_jsonl_file(file_path)
df = pd.DataFrame(data)
save_parquet(save_path, df)