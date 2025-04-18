import json
import uuid
Nfile = "extracted_data.json"
Lfile = "extracted_content.lean"
with open (Lfile, "r") as file:
    Ldata = file.read()
with open (Nfile, "r") as file:
    data = json.load(file)
def extract_data(name, Ldata,problem):
    target_position = Ldata.find(name)
    # 从目标位置向前查找第一个“theorem”的位置
    theorem_position = Ldata.rfind("theorem", 0, target_position)
    sorry_position = Ldata.find(":=\nby", target_position)
    start = theorem_position
    end = sorry_position + len(":=\nby")   # 包括“sorry”
    end2 = Ldata.find(":=", target_position)
    thm = Ldata[start:end]
    goal = Ldata[target_position + len(name) + 3:end2]
    Ldata = Ldata[:theorem_position] + "\n\n--" + name + "\n--" + problem + "\n" + Ldata[theorem_position:]
    print('---------')
    print(name, thm, goal)
    return thm, goal
output = []
header = "import SystemE\nimport UniGeo.Relations\nimport UniGeo.Abbre\n\n"
for item in data:
    name = item["name"]
    tag = str(uuid.uuid4())
    if name not in Ldata:
        continue
    fm, goal = extract_data(name+' ', Ldata,item["problem"])
    info = "\/--" + item["problem"] + "-\/\n"
    x = {
        "uuid" : tag,
        "statement_id" : tag,
        "natural_language" : item["problem"],
        "formal_statement" : header + info + fm,
        "tags" : ["type: Geometry", "Source: UniGeo", f"name: {name}", "category: GeometryLean"],
        
    }
    output.append(x)

with open("data/UniGeoLeanPrompt.jsonl",'w') as file:
    for item in output:
        json_str = json.dumps(item, ensure_ascii=False)
        file.write(json_str + '\n')