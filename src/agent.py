import asyncio
import time
import random
import json
import re
from google import genai
from google.genai import types
from src.config import GOOGLE_API_KEY, MODEL_NAME

class GeminiAgent:
    """
    Gemini 智能体封装。
    包含网络错误自动重试机制和结构化的 Prompt 构造。
    """
    def __init__(self, model_name=MODEL_NAME, api_key=GOOGLE_API_KEY):
        self.client = genai.Client(api_key=api_key, http_options={'timeout': 600000})
        self.model_name = model_name
        self.chat_history = []

    def reset_history(self):
        self.chat_history = []

    def generate(self, prompt, temperature=1.0):
        """Synchronous version of generate."""
        user_msg = types.Content(role="user", parts=[types.Part.from_text(text=prompt)])
        self.chat_history.append(user_msg)
        
        max_net_retries = 5
        
        for attempt in range(1, max_net_retries + 1):
            try:
                response = self.client.models.generate_content(
                    model=self.model_name,
                    contents=self.chat_history,
                    config=types.GenerateContentConfig(temperature=temperature)
                )
                
                reply = response.text
                if not reply:
                    raise ValueError("Empty response from API")

                clean_reply = reply.replace("```lean", "").replace("```", "").strip()
                self.chat_history.append(types.Content(role="model", parts=[types.Part.from_text(text=reply)]))
                return clean_reply

            except Exception as e:
                print(f"      ⚠️ [Network Error] {e}")
                if attempt < max_net_retries:
                    wait_time = (2 ** attempt) + random.uniform(0, 1)
                    print(f"      ⏳ Retrying in {wait_time:.1f}s...")
                    time.sleep(wait_time)
                else:
                    print("      💀 [Fatal] Network retries exhausted.")
                    self.chat_history.pop()
                    return None

    async def generate_async(self, prompt, temperature=1.0):
        """Asynchronous version of generate."""
        user_msg = types.Content(role="user", parts=[types.Part.from_text(text=prompt)])
        self.chat_history.append(user_msg)
        
        max_net_retries = 5
        
        for attempt in range(1, max_net_retries + 1):
            try:
                # The GenAI SDK might not be natively async yet, but we can wrap it
                # or use its async methods if available. The current SDK uses sync calls.
                # To keep it truly async-friendly in a loop, we'd use a thread pool or an async client.
                # For now, we'll keep the call but use await for the sleep.
                response = self.client.models.generate_content(
                    model=self.model_name,
                    contents=self.chat_history,
                    config=types.GenerateContentConfig(temperature=temperature)
                )
                
                reply = response.text
                if not reply:
                    raise ValueError("Empty response from API")

                clean_reply = reply.replace("```lean", "").replace("```", "").strip()
                self.chat_history.append(types.Content(role="model", parts=[types.Part.from_text(text=reply)]))
                return clean_reply

            except Exception as e:
                print(f"      ⚠️ [Network Error] {e}")
                if attempt < max_net_retries:
                    wait_time = (2 ** attempt) + random.uniform(0, 1)
                    print(f"      ⏳ Retrying in {wait_time:.1f}s...")
                    await asyncio.sleep(wait_time)
                else:
                    print("      💀 [Fatal] Network retries exhausted.")
                    self.chat_history.pop()
                    return None

    async def generate_one_off_async(self, prompt, temperature=0.0):
        """Generates a response WITHOUT affecting chat history (Async)."""
        max_net_retries = 3
        for attempt in range(1, max_net_retries + 1):
            try:
                response = self.client.models.generate_content(
                    model=self.model_name,
                    contents=prompt,
                    config=types.GenerateContentConfig(temperature=temperature)
                )
                return response.text.strip()
            except Exception as e:
                if attempt < max_net_retries:
                    await asyncio.sleep(2)
                else:
                    return None

    def generate_one_off(self, prompt, temperature=0.0):
        """Generates a response WITHOUT affecting chat history (Sync)."""
        max_net_retries = 3
        for attempt in range(1, max_net_retries + 1):
            try:
                response = self.client.models.generate_content(
                    model=self.model_name,
                    contents=prompt,
                    config=types.GenerateContentConfig(temperature=temperature)
                )
                return response.text.strip()
            except Exception as e:
                if attempt < max_net_retries:
                    time.sleep(2)
                else:
                    return None

    def inject_context(self, context_text):
        injection = f"\n[SYSTEM CONTEXT INJECTION]\n{context_text}\n"
        self.chat_history.append(types.Content(role="user", parts=[types.Part.from_text(text=injection)]))

    def generate_technical_queries(self, error_msg, task_description):
        """
        [NEW] Advanced Technical Probing. 
        Instead of simple keywords, generates speculative Lean signatures, 
        potential paths, and library-aware technical aliases.
        """
        prompt = f"""
        You are an expert Lean 4 Librarian and Formalization Engineer.
        TASK: {task_description}
        CONTEXT/ERROR: {error_msg[-800:]} (truncated)
        
        Your goal is to generate search parameters to find relevant code in a local Mathlib 4 repository.
        Do NOT generate generic words. Think like a Mathlib developer.
        
        OUTPUT FORMAT:
        Return a strictly valid JSON object with the following keys:
        1. "keywords": (List[str]) 5-10 technical keywords. 
           Example: ["inducedOuterMeasure", "Caratheodory", "is_measurable_field"]
        2. "signatures": (List[str]) 2-3 speculative Lean 4 function/theorem signatures.
           Example: ["theorem measure_extend_unique", "def outer_measure_extension"]
        3. "paths": (List[str]) 2-3 potential Mathlib 4 module paths.
           Example: ["MeasureTheory.Measure", "MeasureTheory.OuterMeasure", "MeasureTheory.Constructions"]
        4. "aliases": (List[str]) 2-3 possible library-specific names for the named theorem/concept.
           Example: ["Hahn-Kolmogorov" -> "Measure.extend"]
           
        JSON ONLY.
        """
        text = self.generate_one_off(prompt, temperature=0.0)
        if not text:
            return {"keywords": [], "signatures": [], "paths": [], "aliases": []}

        try:
            # Clean JSON markdown if present
            text = re.sub(r"```json\s*", "", text)
            text = re.sub(r"```\s*", "", text)
            
            data = json.loads(text)
            return data
        except Exception as e:
            print(f"   ⚠️ [Agent] Technical query generation failed to parse JSON: {e}")
            return {"keywords": [], "signatures": [], "paths": [], "aliases": []}

    def extract_keywords(self, error_msg, task_description):
        """Legacy wrapper for backward compatibility."""
        data = self.generate_technical_queries(error_msg, task_description)
        # Combine everything for the simple keyword search
        all_terms = data.get("keywords", []) + data.get("signatures", []) + data.get("paths", []) + data.get("aliases", [])
        return list(set(all_terms))

    # --- [修改] 升级 Feedback Prompt 结构 ---
    def construct_feedback_prompt(self, error_msg, search_hint="", expert_hints=""):
        """
        构造层次分明的反馈 Prompt。
        search_hint: 通常包含 RAG 检索到的 Mathlib 源码。
        expert_hints: 从 HintManager 匹配到的战术避坑指南。
        """
        clean_error = error_msg
        if len(error_msg) > 2000:
            clean_error = "...(truncated)...\n" + error_msg[-2000:]
            
        # 组装专家经验区块 (软注入)
        hints_block = ""
        if expert_hints:
            hints_block = f"""
=========================================
[SUGGESTED TACTICAL SHIFT (HEURISTICS)]:
The following hints are triggered by your current error. They are heuristic suggestions from past experiences. They might point you in the right direction, but you MUST verify their exact syntax against Mathlib.

{expert_hints}
=========================================
"""

        # 组装源码区块 (硬约束)
        source_block = ""
        if search_hint:
            source_block = f"""
=========================================
[MATHLIB SOURCE REFERENCE (GROUND TRUTH)]:
Here are the actual Mathlib files retrieved from the local repository. You MUST rely on these for exact function signatures and theorem names.

{search_hint}
=========================================
"""

        return f"""
Compilation failed.

[COMPILER ERROR LOG]:
{clean_error}

{hints_block}
{source_block}

TASK:
Fix the code based on the error log. 
1. Consider the [SUGGESTED TACTICAL SHIFT] (if any) to break out of your current flawed approach.
2. ALWAYS verify the exact syntax and theorem names using the [MATHLIB SOURCE REFERENCE] (if provided). Do not blindly hallucinate theorem names.

REQUIREMENT:
You **MUST** start your response with an analysis block like this:

--- ANALYSIS START ---
1. Analysis: Why the previous code failed.
2. Strategy: How you will change your approach (mention if you are adopting the suggested hints).
--- ANALYSIS END ---

Then, return the FULL valid Lean code (starting with imports).
"""
