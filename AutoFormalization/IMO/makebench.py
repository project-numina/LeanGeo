import json
import uuid
Nfile = "data/GeoLeanBench.json"
Lfile = "imobench.lean"
with open (Lfile, "r") as file:
    Ldata = file.read()
with open (Nfile, "r") as file:
    data = json.load(file)
def extract_data(name, Ldata):
    target_position = Ldata.find(name)
    # 从目标位置向前查找第一个“theorem”的位置
    theorem_position = Ldata.rfind("theorem", 0, target_position)
    sorry_position = Ldata.find("sorry", target_position)
    start = theorem_position
    end = sorry_position   # 包括“sorry”
    end2 = Ldata.find(":=", target_position)
    thm = Ldata[start:end]
    goal = Ldata[target_position + len(name) + 3:end2]
    print('---------')
    print(name, thm, goal)
    return thm, goal
output = []
header = "import SystemE\nimport UniGeo.Relations\nimport UniGeo.Abbre\nimport UniGeo.Theorem\n\n"
for item in data:
    name = item["name"]
    tag = str(uuid.uuid4())
    if name not in Ldata:
        continue
    fm, goal = extract_data("problem_"+name, Ldata)
    info = "\/--" + item["natural_language"] + "-\/\n"
    x = {
        "name" : name,
        "split" : "test",
        "informal_prefix" : info,
        "formal_statement" : header + info + fm,
        "goal" : goal,
        "header" : header,
        "formal_proof" : "",
        "uuid" : tag,
        "statementid" : tag,
        "natural_language" : item["natural_language"],
        "data_name":"GeometryLeanBench",
        "category":"GeometryLeanBench"
        
    }
    output.append(x)

with open("data/GeometryLeantest.jsonl",'w') as file:
    for item in output:
        json_str = json.dumps(item, ensure_ascii=False)
        file.write(json_str + '\n')
