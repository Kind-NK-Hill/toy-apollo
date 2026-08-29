import json
import os

class ReflectionManager:
    """
    Manages the 'Lab Notebook' for self-reflection.
    Synthesizes lessons from failed attempts to avoid repeating mistakes.
    """
    def __init__(self, memory_file="lab_notebook.json"):
        self.memory_file = memory_file
        self.notebook = {} # Maps task_id -> list of lessons
        self.load()

    def load(self):
        if os.path.exists(self.memory_file):
            try:
                with open(self.memory_file, "r", encoding="utf-8") as f:
                    self.notebook = json.load(f)
            except:
                self.notebook = {}

    def save(self):
        with open(self.memory_file, "w", encoding="utf-8") as f:
            json.dump(self.notebook, f, indent=4, ensure_ascii=False)

    def add_lesson(self, task_id, error_msg, attempt_code):
        """
        In a real scenario, we might use an LLM to summarize the error into a 'lesson'.
        For now, we store the core error and the attempt index.
        """
        if task_id not in self.notebook:
            self.notebook[task_id] = []
        
        # Simple extraction of the last few lines of the error
        clean_error = error_msg.split('\n')[-3:] 
        lesson = {
            "error_summary": " ".join(clean_error),
            "timestamp": os.path.getmtime(self.memory_file) if os.path.exists(self.memory_file) else 0
        }
        self.notebook[task_id].append(lesson)
        # Keep only the last 5 lessons per task to avoid context bloat
        self.notebook[task_id] = self.notebook[task_id][-5:]
        self.save()

    def get_lessons_prompt(self, task_id):
        """Formats the lessons into a prompt string."""
        if task_id not in self.notebook or not self.notebook[task_id]:
            return ""
        
        prompt = "\n[LAB NOTEBOOK - LESSONS FROM PREVIOUS ATTEMPTS]:\n"
        for i, lesson in enumerate(self.notebook[task_id]):
            prompt += f"{i+1}. Encountered Error: {lesson['error_summary']}\n"
        prompt += "\nDO NOT repeat the same mistakes. Change your strategy if the previous one failed.\n"
        return prompt
