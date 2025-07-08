import json
import uuid
import random
def read_jsonl(file_path):
    if file_path.endswith('.jsonl'):
        try:
            data =[]
            with open(file_path, 'r', encoding='utf-8') as file:
                for line in file:
                    json_data = json.loads(line.strip())
                    data.append(json_data)
            return(data)
        except FileNotFoundError:
            print(f"文件 {file_path} 未找到，请检查路径是否正确。")
        except json.JSONDecodeError as e:
            print(f"解析JSON时出错：{e}")
        except Exception as e:
            print(f"发生其他错误：{e}")
    elif file_path.endswith('.json'):
        try:
            with open(file_path, 'r', encoding='utf-8') as file:
                data = json.load(file)
            return(data)
        except FileNotFoundError:
            print(f"文件 {file_path} 未找到，请检查路径是否正确。")
        except json.JSONDecodeError as e:
            print(f"解析JSON时出错：{e}")
        except Exception as e:
            print(f"发生其他错误：{e}")
    else:
        return("Not a json file!")

Nfile = "extracted_data.json"
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
summary_head = "You are an expert in mathematics and the Lean 4 proof assistant. You will be given a statement of a mathematical theorem in natural language and in Lean 4 and a thinking block, which contains a natural language proof with as well as translation hints to Lean 4 by explaining the use of Lean 4 tactics, reflecting on the proof-steps and the current proof-state. Your task is to generate a summary of the thinking block, which should include a high-level description of the proof paired up with Lean 4 tactics and library lemmas used, focusing on the key points in the proof. You should format your output in a <summary> </summary> block and not use any # characters or code snippets. Lastly, please act as if you do NOT have access to the informal proof and are still working towards formalizing the proof in Lean 4."
num = 0
with open("LeanSFT_CoT_0701.json",'r') as file:
    data = json.load(file)
for item in data:
    num = num + 1
    tag = str(uuid.uuid4())
    item["formal_statement"] = item["formal_statement"].strip()
    #item["formal_proof"] = item["formal_proof"].replace("import LeanGeo", "import LeanGeo\nnamespace LeanGeo\n")
    statement = item["formal_statement"]
    thm_position = statement.find("theorem")
    statement = statement[:thm_position+8] + "G_" + statement[thm_position+8:]
    thm_position = item["formal_proof"].find("theorem")
    item["formal_proof"] = item["formal_proof"][:thm_position+8] + "G_" + item["formal_proof"][thm_position+8:]
   
    #l = statement.find("theorem")
    #statement = statement[:l] + "namespace LeanGeo\n" + "\n" + statement[l:]
    instruction = f"Think about and solve the following problems step by step in Lean 4.\n# Formal Statement:\n\n```lean4\n{statement}\n```\n"
    #summary_prompt = summary_head + f"\n\nNatural language statement: \n\n" + problem + f"\n\nLean4 statement:\n```lean4\n{statement}\n\n```\n<Thinking block>:\n" + item["Gemini_result"]
    #summary = item['summary']
    item["Gemini_result"] = item["Gemini_result"].replace("```lean4","```tactics")
    item["Gemini_result"] = item["Gemini_result"].replace("```lean","```tactics")
    output1 ='<think>\n'+item["Gemini_result"]+ '\n</think>' +'\n```lean4\n'+ item['formal_proof'] + '\n```'
    nl = "You can prove the theorem with the help of the following theorems:\n#Lemmas:\n"
    for i in item["using_lemmas"]:
        nl = nl + i + '\n'
    nl = nl  + '\n\n'
    instruction = nl + instruction

    instruction = instruction.replace("namespace LeanGeo", "namespace LeanGeo\nset_option maxHeartbeats 0")
    statement = statement.replace("namespace LeanGeo", "namespace LeanGeo\nset_option maxHeartbeats 0")
    item['formal_proof'] = item['formal_proof'].replace("namespace LeanGeo", "namespace LeanGeo\nset_option maxHeartbeats 0")
    output1 = output1.replace("namespace LeanGeo", "namespace LeanGeo\nset_option maxHeartbeats 0")

    x = {
        "uuid" : tag,
        "system" : "You are an expert in mathematics and proving theorems in Lean 4.",
        "instruction" : instruction,
        "natural_language":nl,
        "formal_statement":statement,
        "input:" : "",
        "statement_id":str(uuid.uuid4()),
        "formal_proof": item['formal_proof'],
        "summary_prompt": '',
        "summary": '',
        "output": output1,
        "batch_id": num,
        #"tags" : ["type: Geometry", "Source: UniGeo", f"name: {name}", "category: GeometryLean"],
    }
   
    output.append(x)
with open("/home/songchendong/lean/lean0415/geometry/IMO/data/LeanSFTdata.jsonl",'w') as file:
    for item in output:
        json_str = json.dumps(item, ensure_ascii=False)
        file.write(json_str + '\n')