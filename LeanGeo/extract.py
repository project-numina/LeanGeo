import json
import os
def extract_file(filename):
    with open(filename,"r") as f:
        lines = f.readlines()
    data = []
    in_box = 0
    fp = ""
    fm = ""
    in_statement = 0
    extracted_document = ['LeanGeo/Theorem.lean','LeanGeo/BookTheorem.lean']
    filename = filename[filename.find('LeanGeo/'):]
    if filename in extracted_document:
        print(111)
        return []
    for line in lines:
        if line.startswith("theorem"):
            l = line.find(":")
            if in_box == 1:
                data.append({
                "name": name,
                "using_lemmas": lemma,
                "proof_state" : state,
                "formal_statement": fm,
                "formal_proof": fp,
                "source": filename
            })
            in_box = 1
            name = line[8:l].strip()
            state = "whole_proof"
            lemma = []
            fm = line
            fp = line
            in_statement = 1
            if ":= by" in line:
                in_statement = 0
            continue
        if "sorry" in line:
            state = "with_sorry"
        if "euclid_apply" in line:
            thm = line.strip().split(' ')[1]
            lemma.append(thm)
        if in_statement == 1:
            fm = fm +line
        if ":= by" in line:
            in_statement = 0
        fp = fp + line
    if in_box == 1:
        data.append({
                "name": name,
                "using_lemmas": lemma,
                "proof_state" : state,
                "formal_statement": fm,
                "formal_proof": fp,
                "source": filename
            })
    return(data)
d = []
folder_path = '/home/songchendong/lean/LeanEuclid/LeanGeo'  # 替换为你的文件夹路径
# 使用 os.walk() 遍历文件夹
for root, dirs, files in os.walk(folder_path):
    # root 是当前遍历到的文件夹路径
    # dirs 是当前文件夹下的子文件夹列表
    # files 是当前文件夹下的文件列表
    # 打印当前文件夹路径
    print(f"正在遍历文件夹：{root}")
    # 遍历当前文件夹中的文件
    for file in files:
        if file.endswith('.lean'):

            file_path = os.path.join(root, file)  # 获取文件的完整路径
            d.extend(extract_file(file_path))
with open("extracted_data.json","w") as file:
    json.dump(d, file, ensure_ascii=False, indent=4)
            
            



    