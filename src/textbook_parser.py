import json
import re
import time
import random
from google import genai
from google.genai import types
from src.config import GOOGLE_API_KEY

# 你可以在这里自由切换模型
PARSER_MODEL = "gemini-3-pro-preview" 

class TextbookParser:
    def __init__(self, api_key=GOOGLE_API_KEY):
        # 修复 1：增加 10 分钟的超长 Timeout 设置
        self.client = genai.Client(
            api_key=api_key, 
            http_options={'timeout': 600000}
        )
        self.model_name = PARSER_MODEL

    def _clean_json_string(self, raw_text):
        """终极 JSON 清理器"""
        if "```json" in raw_text:
            raw_text = raw_text.split("```json")[1].split("```")[0]
        elif "```" in raw_text:
            raw_text = raw_text.replace("```", "")
            
        fixed_text = re.sub(r'(?<!\\)\\(?!["\\/bfnrt])', r'\\\\', raw_text)
        return fixed_text.strip()

    def parse_chapter(self, latex_content):
        print(f"📚 [TextbookParser] Analyzing and chunking textbook content using {self.model_name}...")
        
        prompt = r"""
        You are an expert Mathematical Editor and Lean 4 Formalization Architect.
        
        INPUT:
        A section of a mathematics textbook in LaTeX format.
        
        TASK:
        Decompose this text into a strictly sequential list of formalization tasks. 
        Lean 4 requires a strict top-down dependency order. You must chunk the text into logical blocks.
        
        CATEGORIES (The "type" field MUST be one of these):
        1. "Definition": Mathematical definitions.
        2. "Theorem_Statement": Major theorems that DO NOT have a proof in the text, OR a theorem statement whose proof appears much later in the text.
        3. "Theorem_with_Proof": A theorem or lemma immediately followed by its proof. Combine them into a SINGLE block.
        4. "Example_Proof": Specific examples, calculations, or a "Delayed Proof" (e.g., "Proof of Theorem 3.3") that appears long after its statement.
        5. "Problem": Exercises.
        6. "Remark": Conversational text.
        
        CRITICAL DEPENDENCY RULES FOR DELAYED PROOFS:
        If you encounter a proof for a theorem stated earlier (e.g., "Proof of Theorem 3.3" appearing after Def 3.6, Thm 3.4, etc.):
        - You MUST classify it as "Example_Proof".
        - Its "dependencies" array MUST strictly include the block_id of the original "Theorem_Statement".
        - Its "dependencies" array MUST also include the block_ids of ANY intermediate lemmas/definitions (e.g., Heine-Borel, Sigma-subadditive) that are explicitly or implicitly used in this proof.

        OUTPUT FORMAT:
        Return a strictly valid JSON list of objects. Each object MUST have:
        - "block_id": A unique string ID (e.g., "def_3_1", "thm_hahn_kolmogorov", "ex_3_1_1", "prob_3_1").
        - "type": One of the 5 categories listed above.
        - "title": A short human-readable title.
        - "content": The EXACT LaTeX text corresponding to this block.
        - "dependencies": A list of "block_id"s that this block explicitly references or relies on.
        
        CRITICAL JSON ESCAPING RULE:
        Because the "content" field contains LaTeX, you MUST double-escape all backslashes in the JSON string.
        For example, `\mathbb{R}` MUST be written as `\\mathbb{R}` in the JSON output.
        
        LATEX CONTENT:
        """ + latex_content + r"""
        
        JSON OUTPUT:
        """
        
        # 修复 2：增加网络重试循环 (最多重试 3 次)
        max_retries = 3
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
                clean_text = self._clean_json_string(result_text)
                    
                blocks = json.loads(clean_text)
                
                # [NEW] Renowned Theorem Detection
                renowned_keywords = [
                    "Hahn-Kolmogorov", "Heine-Borel", "Caratheodory", 
                    "Pi-Lambda", "Dynkin", "Monotone Class", 
                    "Lebesgue-Stieltjes", "Fatou", "Monotone Convergence",
                    "Dominated Convergence", "Borel-Cantelli"
                ]
                
                for b in blocks:
                    content = b.get("content", "")
                    title = b.get("title", "")
                    # Check if any keyword matches content or title
                    if any(kw.lower() in content.lower() or kw.lower() in title.lower() for kw in renowned_keywords):
                        b["is_renowned"] = True
                        print(f"   🏆 [TextbookParser] Tagged renowned theorem: {b.get('block_id')}")
                    else:
                        b["is_renowned"] = False

                print(f"✅ [TextbookParser] Successfully extracted {len(blocks)} logical blocks.")
                return blocks
                
            except json.JSONDecodeError as e:
                print(f"❌ [TextbookParser Error] JSON Decode Failed: {e}")
                print("--- Raw Output Snippet ---")
                print(result_text[:500] + "...\n...\n" + result_text[-500:])
                return [] # JSON 解析失败通常是模型逻辑问题，直接返回空
                
            except Exception as e:
                print(f"   ⚠️ [Network Error] Attempt {attempt}/{max_retries} failed: {e}")
                if attempt < max_retries:
                    wait_time = (2 ** attempt) + random.uniform(0, 1)
                    print(f"   ⏳ Retrying in {wait_time:.1f}s...")
                    time.sleep(wait_time)
                else:
                    print("   💀 [Fatal] Parser network retries exhausted.")
                    return []