import json

def filter_zero_proofs_to_txt(input_file, output_file, sample_size=100):
    count = 0
    with open(input_file, 'r', encoding='utf-8') as infile, \
         open(output_file, 'w', encoding='utf-8') as outfile:
        
        for line in infile:
            if count >= sample_size:
                break
            try:
                data = json.loads(line)
                
                # 检查n_correct_proofs是否为0
                if (data.get("n_correct_proofs") >  0) and (data.get("n_correct_proofs") > 10) :
                    # 递归处理所有字符串的换行符
                    def process_data(obj, indent=0):
                        if isinstance(obj, str):
                            return obj.replace('\\n', '\n' + ' ' * indent)
                        elif isinstance(obj, dict):
                            return '\n'.join(
                                f"{' ' * indent}{k}:" + (
                                    f"\n{process_data(v, indent + 4)}" 
                                    if isinstance(v, (dict, list)) 
                                    else f" {process_data(v)}"
                                )
                                for k, v in obj.items()
                            )
                        elif isinstance(obj, list):
                            return '\n'.join(
                                f"{' ' * indent}- {process_data(item, indent + 2)}" 
                                for item in obj
                            )
                        return str(obj)
                    
                    # 写入格式化后的数据
                    outfile.write(process_data(data) + '\n\n')
                    count += 1
                    
            except json.JSONDecodeError:
                continue
    
    print(f"成功筛选 {count} 条n_correct_proofs=0的数据到 {output_file}")

# 使用示例
filter_zero_proofs_to_txt('data/trainAIMO.json', 'zero_proofs_data.txt')