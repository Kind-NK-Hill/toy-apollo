import os
import json
import re
from pathlib import Path
from tqdm import tqdm
import faiss
import numpy as np
from sentence_transformers import SentenceTransformer
from src.config import MATHLIB_PATH

class MathlibIndexer:
    def __init__(self, model_name="all-MiniLM-L6-v2", index_path="mathlib_index.faiss", corpus_path="mathlib_corpus.json"):
        try:
            # Try loading locally first to avoid network timeouts (version checks)
            self.model = SentenceTransformer(model_name, local_files_only=True)
        except Exception:
            # Fallback to online if not found locally
            print(f"ℹ️ [Indexer] Model not found locally, attempting to download...")
            self.model = SentenceTransformer(model_name)
        
        self.dimension = self.model.get_sentence_embedding_dimension()
        self.index_path = index_path
        self.corpus_path = corpus_path
        self.index = None
        self.corpus = []

    def _extract_theorems_from_file(self, file_path: Path) -> list:
        """
        Extracts theorem/lemma/def names and their immediate context from a Lean file.
        Using regex for a balance of speed and coverage.
        """
        theorems = []
        try:
            content = file_path.read_text(encoding="utf-8")
            # Matches: theorem/lemma/def/instance/structure/class <name> ...
            # We capture the name and a bit of the following text (the statement)
            pattern = r"(theorem|lemma|def|instance|structure|class)\s+([^\s\(\{\:]+)"
            matches = re.finditer(pattern, content)
            
            # Determine import path
            try:
                rel_path = file_path.relative_to(Path(MATHLIB_PATH).parent)
                import_path = str(rel_path).replace(os.path.sep, ".").replace(".lean", "")
            except:
                import_path = file_path.name

            for match in matches:
                name = match.group(2)
                # Skip internal or anonymous names
                if name.startswith("_") or "._" in name:
                    continue
                
                start_idx = match.start()
                # Grab up to 400 chars of context for embedding
                statement_context = content[start_idx : start_idx + 400].strip()
                
                theorems.append({
                    "name": name,
                    "import": import_path,
                    "statement": statement_context,
                    "file": str(file_path)
                })
        except Exception as e:
            # print(f"Error reading {file_path}: {e}")
            pass
        return theorems

    def build_index(self, mathlib_root: str):
        """Walks through Mathlib and builds the FAISS index."""
        print(f"🔍 [Indexer] Scanning Mathlib at {mathlib_root}...")
        all_theorems = []
        lean_files = list(Path(mathlib_root).rglob("*.lean"))
        
        for file_path in tqdm(lean_files, desc="Extracting theorems"):
            all_theorems.extend(self._extract_theorems_from_file(file_path))
        
        print(f"✅ Found {len(all_theorems)} theorems/definitions.")
        self.corpus = all_theorems

        # Prepare texts for embedding
        # We combine name and statement for better semantic search
        texts = [f"Theorem: {t['name']}\nImport: {t['import']}\n{t['statement']}" for t in all_theorems]
        
        print("🧠 [Indexer] Generating embeddings (this may take a while)...")
        # Process in batches to save memory
        embeddings = self.model.encode(texts, batch_size=64, show_progress_bar=True, convert_to_numpy=True)
        
        # Normalize for cosine similarity
        faiss.normalize_L2(embeddings)
        
        print("💾 [Indexer] Creating FAISS index...")
        self.index = faiss.IndexFlatIP(self.dimension)
        self.index.add(embeddings)
        
        # Save
        faiss.write_index(self.index, self.index_path)
        with open(self.corpus_path, "w", encoding="utf-8") as f:
            json.dump(self.corpus, f, ensure_ascii=False, indent=2)
        
        print(f"✨ Index saved to {self.index_path}, Corpus saved to {self.corpus_path}")

    def load(self):
        """Loads index and corpus from disk."""
        if os.path.exists(self.index_path) and os.path.exists(self.corpus_path):
            self.index = faiss.read_index(self.index_path)
            with open(self.corpus_path, "r", encoding="utf-8") as f:
                self.corpus = json.load(f)
            return True
        return False

if __name__ == "__main__":
    # Test/Run Indexing
    indexer = MathlibIndexer()
    indexer.build_index(MATHLIB_PATH)
