import os
import subprocess
import json
from concurrent.futures import ThreadPoolExecutor, as_completed

# 输入文件路径
json_file = "data/Numina_Geometry_all.json"
from openai import OpenAI
pass_at = 1
api_key = "sk-UqsUV3Gsprv60YNoeCUeIRdH2jWp7AqEKjW7CDvnWvi2BXlY"
#base_url = "https://autoformalization.app.msh.team/v1"
base_url = "https://openai.app.msh.team/v1"
import datetime
client = OpenAI(
    api_key=api_key, 
    base_url=base_url
)
# 查看支持的模型
models = client.models.list()
print(models) 

# 对话api
def get_ai_response(prompt, system, number):
    message = []
    message.append({"role": "system", "content" : system})
    message.append({"role": "user", "content": prompt})
    print(prompt)
    try:
        # 创建聊天完成请求
        import time
        time.sleep(0.1)
        completion = client.chat.completions.create(
            model="o1-2024-12-17",  
            messages=message,
            n = number
        )
        # 返回 AI 的回复
        result = []
        print(len(completion.choices))
        for i in range(number):
            result.append(completion.choices[i].message.content)
        return result
    except Exception as e:
        return f"发生错误: {str(e)}"

# 测试代码
if __name__ == "__main__":
    # 测试一些问题
    prompt = r"""
- Role: Expert in Formalizing Plane Geometry Theorems
- Background: The user needs to translate plane geometry theorems described in natural language into Lean4 to achieve more precise mathematical expression and logical reasoning. The user has already provided detailed explanations of the formal language and translation examples, but requires assistance to complete the specific translation tasks.
- Profile: You are an expert proficient in plane geometry and Lean4, capable of accurately understanding geometric concepts in natural language and converting them into logical formal expressions. You have a profound understanding of the structure of geometric theorems and the rules of formal language.
- Goals: Based on the natural language plane geometry theorems provided by the user, accurately translate them into formal language, ensuring that the translation results comply with the rules and logical structure of formal language, avoiding translation errors.
- OutputFormat: The translation result should be output in the specified format that follow the grammar rule of Lean4, including the definition of each point and the expression of conclusions, ensuring that the format is standardized and clear.

- Workflow:
  1. Carefully read the natural language description of the plane geometry theorem to understand the geometric elements and logical relationships in the problem.
  2. According to the rules of formal language, gradually convert the geometric elements and conditions in natural language into formal expressions, ensuring that each point's definition does not exceed two constraints.
  3. Check the translation result to ensure the correct use of predicates, accurate number of parameters, and compliance with the logical structure of formal language.
  4. Output the translation result in the specified format and provide necessary explanations and interpretations to help the user understand the translation process.

--Translation Rules:
/- Basic Geometric Sorts -/ : 
axiom Point : Type
axiom Line : Type
axiom Circle : Type
/- Notations and Macros for Geometric Entities -/
"|(a─b)|" means the length of the line segment between point a and point b.
"∠ a:b:c" means the degree of the angle formed by three points a, b, and c.
" ∟" means the right angle.

/- Relations and Axioms for Geometric Sorts -/
For the following rules, you should use "X.predicate Y Z ..." to translate, for example, 'a.onLine L' means a is on line L.
/-
def onLine (a : Point) (L : Line) -- point a is on line L.
def sameSide (a b : Point) (L : Line) -- point a and b are on the same side of line L.
def opposingSides (a b : Point) (L : Line) -- point a and b are on the opposite sides of line L.
def onCircle (a: Point) (C: Circle) -- point a is on circle C.
def insideCircle (a: Point) (C: Circle) -- point a is inside circle C.
def outsideCircle (a: Point) (C: Circle)-- point a is outside circle C.
def isCentre (a: Point) (C: Circle) -- point a is on the center circle C.
def intersectsCircle (C1 C2: Circle) -- circle C1 and C2 intersect.
-/

For the following rules, you should use "predicate X Y Z ..." to translate, for example, cyclic X Y Z W means Point X Y Z W are in the same circle.
/-
def distinctPointsOnLine (a b : Point) (L : Line) -- points a and b are distinct and on line L.
def twoLinesIntersectAtPoint (AB BC : Line) (b : Point) -- line AB and BC intersect at point b.
def between (a b c : Point) -- points a, b and c collinear and cyclically ordered.
def formTriangle (a b c : Point) (AB BC CA : Line) -- point a, b and c form a triangle, where point a and b are on line AB, point b and c are on line BC, point a and c are online CA.
def coll (A B C : Point) -- Point a b c are collinear.
def triangle (A B C : Point) -- Point a b c form a triangle.
def isoTriangle (A B C : Point) -- Point a b c form a isosceles triangle where |(A─B)| = |(A─C)|.
def rightTriangle (A B C : Point) -- Point a b c form a right triangle where ∠B:A:C = ∟.
def circumCentre (O A B C : Point) -- O is the circumcenter of triangle ABC.
def circumCircle (Ω : Circle) (A B C : Point) -- \Omega is the circumcircle of triangle ABC.
def abbrev inCentre (I A B C : Point) -- I is the incenter of triangle ABC.
def inCircle (Ω : Circle) (AB BC CA : Line) -- \Omega is the incircle of the triangle mad by line AB BC CA.
def perpLine (L M : Line) -- Line L and M are perpendicular
def perpBisector (a b : Point) (L : Line)  -- Line L is the perpendicular bisector of segment ab.
def midpoint (A P B : Point) -- Point P is the midpoint of line AB.
def cyclic (A B C D: Point) -- Point A B C D are in the same circle
def formQuadrilateral (A B C D : Point) (AB BC CD DA : Line) --ABCD is a convex quadrilateral.
def tangentLine (L : Line) (O : Circle) -- Line L is tangent to circle O.
def tangentAtPoint (L : Line) (O :Circle) (P : Point) -- Line L is tangent to Circle O at Point P.
def threePointsOnLine (A B C : Point) (L : Line) -- A, B, C are three distinct points on line L.
def insideTriangle (X A B C : Point) (AB BC CA: Line) -- X is in the triangle ABC.
def insideQuadrilateral (X A B C D: Point) (AB BC CD DA: Line) -- X is in the quadrilateral ABCD.

-/
-- Examples:
Below are some pairings of formal problem statements and problems: 

<exterior_angle_triangle> Any exterior angle of a triangle is congruent to the sum of the interior angles not supplementary to it.
<Lean statement> theorem exterior_angle_triangle : ∀ (a b c d: Point), (triangle a b c) ∧ (between a b d) → ∠d:b:c = ∠b:c:a + ∠c:a:b := by
sorry

<diameter_righAngle> The angle correspons to the diameter of a circle is a right angle.
theorem diameter_rightAngle  ∀ (a b c: Point) (C: Circle), (diameter a b C) ∧ (c.onCircle C) ∧ (c ≠ a) ∧ (c ≠ b) → ∠ a:c:b = ∟ := by
sorry
/- Guidelines: -/
1. Proposition Format: Your proposition must be of the form <<< theorem <problem_name> : ∀ (...) P_1 ∧ P_2 ... ∧
P_n → Q_1 ∧ Q_2 ... ∧ Q_m := by sorry >>> where where each P_i and Q_i is built from
the above building blocks using conjunction (∧) disjunction (∨) and negation (¬). Note that there may be zero existentially quantified variables. The <problem_name> should be exactly the same with the problem.
2. Implication: There can be only a single implication in the formula; either side of the
implication must be a conjunction of formulae.
3. Numeric Values Restrictions: Denote 90-degree angle by ∟, 180-degree angle by ∟ + ∟, etc. Also, when referring to segments, we always mean its length (i.e. |(a--b)|).
4. Quantified Variables: Your quantified variables must be limited to primitive geometric
types: points, lines, and circles. ALL bound variables must be mentioned at some point.
5. Intermediate Variables: You should never define an intermediate variable inside the
proposition. For example, "let X := (something);" is NOT allowed.
6. Axioms: You should only use the provided axioms. For example, Line L is parallel to
line M can be expressed as ¬(L.intersectsLine M). Do not use Line.Parallel L M.
7. Do not add any annotations/explanations, or markdown.
8. You should be careful to two diffenrent kinds of rules. For example, use "a.onLine L" but not "onLine a L", use "a.isCentre C" but not "isCentre a C".
syntax.
9. If statement contains "A is on side BC" you should translate it as "between B A C" but not onLine or coll.
-- Task:
    Please translate the following problem according to workflow. Carefully consider the --Tips and follow the  output format. Think carefully and step by step.
"""
    
    # 读取 JSON 文件
    questions = []
    with open(json_file, "r", encoding="utf-8") as f:
        data = json.load(f)

    for idx, entry in enumerate(data):
        problem = entry.get("problem", "未知问题")
        name = entry.get("name", f"idx")
        if idx < 100:
            questions.append(f"<{name}> \n    {problem} \n\n")
    #txt2 ="以下是一个翻译结果的验证器给你翻译的反馈，请根据反馈修改你的翻译，并给出修改后的翻译："
    # 循环提问并获取回答"

    #globalmessage = []
    file = []
    with ThreadPoolExecutor(max_workers=512) as executor:
        futures = {executor.submit(get_ai_response, question, prompt, pass_at): question for question in questions}
        for future in as_completed(futures):
            try:
                answer = future.result()
                file.append(answer)
            except Exception as e:
                print(f"Error processing question: {futures[future]}")
                print(f"Error: {e}")   
    head = "import SystemE\nimport UniGeo.Relations\nimport UniGeo.Abbre\nimport UniGeo.Theorem\n"
    with open("trans_Kiselev.lean", "w") as log_file:
        log_file.write(head)
        for problem in file:
            for line in problem:
                log_file.write(line + "\n\n")
