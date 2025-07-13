import os
import json

def extract_txt_to_json(folder_path, output_file):
    """
    遍历指定文件夹及其子文件夹，提取所有 .txt 文件的内容，并将其保存为 JSON 格式。

    Args:
        folder_path (str): 要遍历的文件夹路径
        output_file (str): 保存提取内容的输出 JSON 文件路径
    """
    # 检查文件夹是否存在
    if not os.path.exists(folder_path):
        print(f"文件夹 '{folder_path}' 不存在！")
        return

    # 检查输出文件夹是否存在，如果不存在则创建
    output_dir = os.path.dirname(output_file)
    if output_dir and not os.path.exists(output_dir):
        os.makedirs(output_dir)

    # 用于存储提取的内容
    extracted_data = []

    # 遍历文件夹及其子文件夹
    for root, dirs, files in os.walk(folder_path):
        for file in files:
            # 检查文件是否是 .txt 文件
            if file.endswith(".txt"):
                file_path = os.path.join(root, file)
                try:
                    # 读取文件内容
                    with open(file_path, 'r', encoding='utf-8') as f:
                        content = f.read()

                    # 提取文件名（不包含路径）
                    file_name = os.path.basename(file_path)
                    print(file_name,file_path)
                    y = file_path.split('/')
                    z = file_name.split('.')
                    type = y[-2]
                    name = y[-3]+'_Thm'+z[0].zfill(2)
                    if y[-2] == "proofs" :
                        continue
                    p = 0
                    # 将文件名和内容添加到数据列表
                    for item in extracted_data:
                        if item["name"] == name:
                            p = 1
                    if p == 0 :
                        extracted_data.append({
                            "name": name,
                            "problem": content.strip()
                        })
                    else:
                        for item in extracted_data:
                            if item["name"] == name:
                                x = item["problem"]
                                if type == "diagrams2texts":
                                    item["problem"] = content.strip() + x
                                else:
                                    item["problem"] = x + content.strip()
                        print(p,type,x,content.strip() )

                except Exception as e:
                    print(f"处理文件 '{file_path}' 时出错: {e}")

    # 将提取的数据写入 JSON 文件
    if extracted_data:
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(extracted_data, f, ensure_ascii=False, indent=4)
        print(f"提取完成，结果已保存到 '{output_file}'")
    else:
        print("没有找到符合条件的 .txt 文件。")

if __name__ == "__main__":
    # 指定要遍历的文件夹路径
    folder_path = "/home/songchendong/lean/LeanEuclid/UniGeo"
    # 指定输出 JSON 文件路径
    output_file = "extracted_data.json"
    
    # 调用函数
    extract_txt_to_json(folder_path, output_file)