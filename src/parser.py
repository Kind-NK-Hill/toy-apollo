from google import genai
from google.genai import types
from src.config import GOOGLE_API_KEY

# 使用最快、最便宜的模型进行清洗
PARSER_MODEL = "gemini-2.0-flash-exp"

class CodeParser:
    def __init__(self, api_key=GOOGLE_API_KEY):
        self.client = genai.Client(api_key=api_key)

    def extract_lean_code(self, raw_text):
        """
        使用 LLM 从混合文本中提取纯净的 Lean 代码。
        """
        # 1. 快速预处理：如果看起来已经很干净，就不调用 LLM (省钱省时)
        if "--- ANALYSIS" not in raw_text and "```" not in raw_text and len(raw_text) < 5000:
             # 简单的启发式检查：如果开头就是 import 或 def，可能不需要清洗
             if raw_text.strip().startswith("import") or raw_text.strip().startswith("def"):
                 return raw_text.strip()

        # 2. 调用 LLM 进行清洗
        prompt = f"""
        You are a code extraction tool.
        
        INPUT TEXT:
        {raw_text}
        
        TASK:
        Extract ONLY the valid Lean 4 code from the input.
        - Remove all "Analysis" sections.
        - Remove all Markdown backticks (```lean ... ```).
        - Remove all conversational text.
        - Keep comments that are part of the code (`/-- ... -/` or `-- ...`).
        
        OUTPUT:
        Return ONLY the code. Do not say "Here is the code".
        """
        
        try:
            response = self.client.models.generate_content(
                model=PARSER_MODEL,
                contents=prompt,
                config=types.GenerateContentConfig(temperature=0.0) # 零温确保准确
            )
            return response.text.strip()
        except Exception as e:
            print(f"   ⚠️ [Parser Error] Failed to extract code: {e}")
            # 降级处理：尝试简单的 markdown 清理
            return raw_text.replace("```lean", "").replace("```", "").strip()