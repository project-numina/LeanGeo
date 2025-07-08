import json
import os
import uuid
def extract_file(filename):
    with open(filename,"r") as f:
        lines = f.readlines()
    data = []
    in_box = 0
    fp = ""
    fm = ""
    header = "import Mathlib\nimport SystemE\nimport LeanGeo\nnamespace LeanGeo\n\n"
    in_statement = 0
    extracted_document = ['github/geometry/LeanGeo/Theorem/BookTheorem.lean','BookTheorem_rename.lean']
    filename = filename[filename.find('lean/'):]
    if filename in extracted_document or 'Book' in filename:
        print(111)
        return []
    lemma = []
    for line in lines:
        if line.startswith("--") or line.startswith("/--") or line.startswith("end"): continue
        if line.startswith("theorem"):
            l = line.find(":")
            if in_box == 1:
                data.append({
                "name": name,
                "using_lemmas": lemma,
                "proof_state" : state,
                "formal_statement": fm.strip(),
                "formal_proof":fp.strip(),
                "source": filename
            })
            in_box = 1
            name = line[8:l].strip()
            state = "whole_proof"
            lemma = []
            fm = line
            fp = line
            in_statement = 1
            if "by" in line:
                in_statement = 0
            continue
        if "sorry" in line:
            state = "with_sorry"
        if "euclid_apply" in line:
            thm = line.strip().split(' ')[1]
            thm = thm.replace("(","")
            lemma.append(thm)
        if in_statement == 1:
            fm = fm +line
        if "by" in line:
            in_statement = 0
        fp = fp + line
    if in_box == 1:
        fm = header + fm.strip()
        fp = header + fp.strip()
        instruction = f"Think about and solve the following problems step by step in Lean 4.\n# Formal Statement:\n\n```lean4\n{fm}\n```\n"
        data.append({
                "name": name,
                "uuid": str(uuid.uuid4()),
                "statement_id": str(uuid.uuid4()),
                "system" : "You are an expert in mathematics and proving theorems in Lean 4.",
                "instruction" : instruction,
                "natural_language":"",
                "formal_statement":fm
                #"proof_state":state
                #"formal_proof":fp,
                #"source": filename
            })
    return(data)
d = []
path_dict =['/home/songchendong/lean/github/geometry/IMO/Bench'] # 替换为你的文件夹路径
# 使用 os.walk() 遍历文件夹
for folder_path in path_dict:
    for root, dirs, files in os.walk(folder_path):
    # root 是当前遍历到的文件夹路径
    # dirs 是当前文件夹下的子文件夹列表
    # files 是当前文件夹下的文件列表
    # 打印当前文件夹路径
    # 遍历当前文件夹中的文件
        for file in files:
            if file.endswith('.lean'):
                file_path = os.path.join(root, file)  # 获取文件的完整路径
                d.extend(extract_file(file_path))
data = []
for item in d:
    data.append(item)
with open("LeanGeoBench.jsonl",'w') as file:
    for item in data:
        json_str = json.dumps(item, ensure_ascii=False)
        file.write(json_str + '\n')

            



    