import os

GOOGLE_API_KEY = os.getenv("GOOGLE_API_KEY", "")
MODEL_NAME = os.getenv("MODEL_NAME", "gemini-3-flash-preview")
ARCHITECT_MODEL_NAME = os.getenv("ARCHITECT_MODEL_NAME", "gemini-3-pro-preview")

PROJECT_ROOT = "."
MATHLIB_PATH = os.path.join(".lake", "packages", "mathlib", "Mathlib")

MAX_FAST_RETRIES = 15
MAX_DEEP_RETRIES = 5

ARISTOTLE_API_KEY = os.getenv("ARISTOTLE_API_KEY", "")
