import json
import time
import random
import re
from google import genai
from google.genai import types
from src.config import GOOGLE_API_KEY, ARCHITECT_MODEL_NAME

class ProofArchitect:
    """
    架构师 Agent：负责将长篇自然语言证明拆解为可执行的 Lean 4 子任务 (Helper Lemmas)。
    """
    def __init__(self, api_key=GOOGLE_API_KEY):
        self.client = genai.Client(api_key=api_key, http_options={'timeout': 600000})
        self.model_name = ARCHITECT_MODEL_NAME 

    def _clean_json_string(self, raw_text):
        """
        终极 JSON 清理器：专门处理包含 LaTeX 的 LLM 输出。
        """
        if "```json" in raw_text:
            raw_text = raw_text.split("```json")[1].split("```")[0]
        elif "```" in raw_text:
            raw_text = raw_text.replace("```", "")
            
        # 将所有单反斜杠替换为双反斜杠，防止 JSON 解析崩溃
        fixed_text = re.sub(r'(?<!\\)\\(?!["\\/bfnrt])', r'\\\\', raw_text)
        return fixed_text.strip()

    def generate_plan(self, latex_content, parent_block_id="complex_proof"):
        print(f"🧠 [Architect] Decomposing complex proof into sub-lemmas...")
        
        # 使用 r""" 防止 Python 自身的转义警告
        prompt = r"""
        You are a Senior Lean 4 Formalization Architect.
        
        INPUT:
        A complex mathematical proof in LaTeX format that a standard LLM failed to prove in one shot.
        
        TASK:
        Decompose this proof into a sequence of **achievable, sequential sub-tasks (Helper Lemmas)**.
        The goal is to reconstruct the proof in Lean 4 step-by-step.
        
        STRATEGY:
        1. **Helper Lemmas**: Isolate small logical steps into independent lemmas.
        2. **Final Assembly**: The final step MUST be the main theorem itself, which should now be easy to prove by simply applying the helper lemmas you just defined.
        
        OUTPUT FORMAT:
        Return a strictly valid JSON list of objects. Each object represents a sub-task and MUST have:
        - "block_id": A deterministic string ID that MUST follow the pattern: "{parent_block_id}_lemma_" + index (e.g., "{parent_block_id}_lemma_1", "{parent_block_id}_lemma_2"). The final task should be "{parent_block_id}_main".
        - "type": MUST be "Example_Proof".
        - "title": A short human-readable title.
        - "domain": The mathematical domain (e.g., "SetTheory", "MeasureTheory").
        - "content": A clear, self-contained mathematical description.
        
        CRITICAL JSON ESCAPING RULE:
        Because the "content" field contains LaTeX, you MUST double-escape all backslashes in the JSON string.
        For example, `\mathbb{R}` MUST be written as `\\mathbb{R}` in the JSON output.
        
        LATEX CONTENT:
        """ + latex_content + r"""
        
        JSON OUTPUT:
        """
        
        max_retries = 5
        for attempt in range(1, max_retries + 1):
            try:
                response = self.client.models.generate_content(
                    model=self.model_name,
                    contents=prompt,
                    config=types.GenerateContentConfig(
                        temperature=0.0, 
                        response_mime_type="application/json" 
                    )
                )
                
                result_text = response.text
                # 调用清理器
                clean_text = self._clean_json_string(result_text)
                    
                plan = json.loads(clean_text)
                print(f"📋 [Architect] Successfully decomposed into {len(plan)} sub-tasks.")
                return plan
                
            except json.JSONDecodeError as e:
                print(f"      ❌ [Architect Error] JSON Decode Failed: {e}")
                # 打印出坏掉的 JSON 方便调试
                print("      --- Raw Output Snippet ---")
                print(result_text[:300] + "...\n...\n" + result_text[-300:])
                
            except Exception as e:
                print(f"      ⚠️ [Architect Network Error] {e}")
                
            if attempt < max_retries:
                wait_time = (2 ** attempt) + random.uniform(0, 1)
                print(f"      ⏳ Retrying in {wait_time:.1f}s...")
                time.sleep(wait_time)
            else:
                print("      💀 [Fatal] Architect retries exhausted.")
                return []
            
    def restate_task(self, latex_content):
        """
        [新增] 错题重述：将失败的、晦涩的 LaTeX 重新表述为更清晰的数学指令。
        """
        print(f"🧠 [Architect] Restating unsolved problem for better clarity...")
        prompt = f"""
        You are an expert Mathematics Professor. 
        An AI coding agent failed to formalize the following LaTeX text into Lean 4. 
        The failure might be due to implicit assumptions, missing context, or confusing notation in the original text.
        
        ORIGINAL LATEX:
        {latex_content}
        
        TASK:
        Rewrite and clarify this mathematical statement. 
        1. Make all implicit assumptions explicit.
        2. Clarify the types of variables (e.g., is it a Real, a Set, a Measure?).
        3. Break down complex sentences into simple, logical bullet points.
        4. Do NOT write Lean code. Just provide a crystal-clear English mathematical description.
        
        OUTPUT:
        Return ONLY the clarified text.
        """
        try:
            response = self.client.models.generate_content(
                model=self.model_name,
                contents=prompt,
                config=types.GenerateContentConfig(temperature=0.2)
            )
            return response.text.strip()
        except Exception as e:
            print(f"      ⚠️ [Architect] Failed to restate task: {e}")
            return latex_content # 如果失败，返回原文