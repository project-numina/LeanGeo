import os
import re

def extract_content_between_keywords(folder_path, output_file):
    """
    遍历指定文件夹及其子文件夹，提取文件中"theorem"和"euclid_finish"之间的内容。

    Args:
        folder_path (str): 要遍历的文件夹路径
        output_file (str): 保存提取内容的输出文件路径
    """
    # 检查文件夹是否存在
    if not os.path.exists(folder_path):
        print(f"文件夹 '{folder_path}' 不存在！")
        return

    # 检查输出文件夹是否存在，如果不存在则创建
    output_dir = os.path.dirname(output_file)
    if output_dir and not os.path.exists(output_dir):
        os.makedirs(output_dir)

    # 正则表达式，用于匹配"theorem"和"euclid_finish"之间的内容
    pattern = re.compile(r'(: ∀.*?)end UniGeo', re.DOTALL)

    # 用于存储提取的内容
    extracted_content = []

    # 遍历文件夹及其子文件夹
    for root, dirs, files in os.walk(folder_path):
        for file in files:
            file_path = os.path.join(root, file)
            try:
                # 读取文件内容
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()

                # 使用正则表达式查找匹配的内容
                matches = pattern.findall(content)
                if matches:
                    # 添加文件路径到提取内容列表
                    f = file_path.split("/")
                    file_path = f[-2] + "_" + f[-1][:-5] + ' '
                    # 添加匹配到的内容到提取内容列表
                    for match in matches:
                        extracted_content.append(f"theorem {file_path}" + match.strip())
                        extracted_content.append("\n")
                    extracted_content.append("\n")

            except Exception as e:
                print(f"处理文件 '{file_path}' 时出错: {e}")

    # 将提取的内容写入输出文件
    if extracted_content:
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write("import SystemE \nimport UniGeo.Relations\n import Book\n\n")
            f.write("\n".join(extracted_content))
        print(f"提取完成，结果已保存到 '{output_file}'")
    else:
        print("没有找到符合条件的内容。")

if __name__ == "__main__":
    # 指定要遍历的文件夹路径
    folder_path = "/home/songchendong/lean/LeanEuclid/UniGeo"
    # 指定输出文件路径
    output_file = "extracted_content.lean"
    
    # 调用函数
    extract_content_between_keywords(folder_path, output_file)