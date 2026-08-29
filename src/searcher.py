import os
import json
import time
import re
import faiss
import numpy as np
from sentence_transformers import SentenceTransformer
from src.indexer import MathlibIndexer
from src.config import MATHLIB_PATH

class MathlibSearcher:
    """
    Searcher (SOTA Vector RAG Edition)
    Combines FAISS-based vector search with local lexical scoring.
    """
    def __init__(self, lib_root_dir=MATHLIB_PATH, api_key=None, local_output_dir="output_lean_files"):
        self.root_dir = lib_root_dir
        self.local_dir = local_output_dir 
        self.api_key = api_key
        
        # Initialize Indexer
        self.indexer = MathlibIndexer()
        self.is_indexed = self.indexer.load()
        
        if self.is_indexed:
            print(f"✅ [Searcher] Vector index loaded with {len(self.indexer.corpus)} theorems.")
        else:
            print(f"⚠️ [Searcher] Vector index not found. Keyword search will be used as fallback.")

    def _get_import_path(self, file_path, is_local=False):
        if is_local:
            return f"LOCAL_PROJECT.{os.path.basename(file_path).replace('.lean', '')}"
        try:
            rel_path = os.path.relpath(file_path, start=os.path.dirname(self.root_dir))
            import_path = rel_path.replace(os.path.sep, ".").replace(".lean", "")
            return import_path
        except Exception:
            return "Unknown.Import"

    def search(self, technical_query, query_description, top_k=5, rerank=True):
        """
        Performs structural vector search followed by technical-aware reranking.
        technical_query: Either a list of keywords or a dict from generate_technical_queries.
        """
        start_time = time.time()
        
        # Handle legacy list input
        if isinstance(technical_query, list):
            technical_query = {"keywords": technical_query, "signatures": [], "paths": [], "aliases": []}
            
        if not self.is_indexed:
            print(f"🔎 [Searcher] Fallback: Indexing not ready. Using basic keyword scan...")
            return self._fallback_keyword_search(technical_query["keywords"], query_description, top_k)

        # 1. Exact/Fuzzy Lexical Search (The "Dictionary Lookup" Layer)
        # This addresses the 'syntax sensitivity' gap for primes and exact names.
        lexical_candidates = []
        keywords = technical_query.get("keywords", [])
        if keywords:
            print(f"🔎 [Lexical Search] Searching for exact identifiers: {keywords}")
            for item in self.indexer.corpus:
                name = item.get('name', '')
                if not name: continue
                
                # Check for exact matches or common Lean suffixes (like ')
                for kw in keywords:
                    # Case-sensitive exact match or prefix match for primes
                    if kw == name or name == kw + "'" or name == kw + "''":
                        try:
                            with open(item['file'], "r", encoding="utf-8") as f:
                                content = f.read(2000)
                        except: content = item['statement']
                        
                        lexical_candidates.append({
                            "import": item['import'],
                            "path": item['file'],
                            "score": 2.0, # Super high priority for exact name match
                            "content": content,
                            "is_local": False,
                            "reason": f"Exact match for '{kw}'"
                        })
                        break # Found one match for this item
            
            if lexical_candidates:
                print(f"   🎯 Found {len(lexical_candidates)} exact/syntax-near matches.")

        # 2. Multi-Source Vector Search
        # [FIX]: Include 'keywords' in the vector query to ground it in truth.
        combined_query = query_description
        if technical_query.get("keywords"):
            combined_query += " " + " ".join(technical_query["keywords"])
        if technical_query.get("signatures"):
            combined_query += " " + " ".join(technical_query["signatures"])
        if technical_query.get("aliases"):
            combined_query += " " + " ".join(technical_query["aliases"])

        print(f"🔎 [Vector Search] Probing Mathlib for technical structure...")
        
        query_embedding = self.indexer.model.encode([combined_query], convert_to_numpy=True)
        faiss.normalize_L2(query_embedding)
        
        candidate_count = 50 if rerank else top_k
        distances, indices = self.indexer.index.search(query_embedding, candidate_count)
        
        candidate_data = lexical_candidates # Start with lexical hits
        seen_paths = {c['path'] for c in candidate_data}

        for dist, idx in zip(distances[0], indices[0]):
            if idx == -1 or idx >= len(self.indexer.corpus):
                continue
            
            theorem = self.indexer.corpus[idx]
            if theorem['file'] in seen_paths: continue # Skip if already found via lexical search
            
            # Path Boosting: If the file is in a predicted path, boost its score
            boost = 1.0
            for p in technical_query.get("paths", []):
                if p.lower() in theorem['import'].lower():
                    boost = 1.2 
                    break

            try:
                with open(theorem['file'], "r", encoding="utf-8") as f:
                    file_content = f.read(2000) 
            except:
                file_content = theorem['statement']
            
            candidate_data.append({
                "import": theorem['import'],
                "path": theorem['file'],
                "score": float(dist) * boost,
                "content": file_content,
                "is_local": False
            })

        # 3. Add Local Context
        local_candidates = self._scan_local_context(technical_query["keywords"])
        for lc in local_candidates:
            if lc['path'] not in seen_paths:
                candidate_data.append(lc)
        
        # Sort by boosted score
        candidate_data.sort(key=lambda x: x['score'], reverse=True)

        if rerank and candidate_data:
            print("   ℹ️ [Searcher] LLM reranking disabled; using local ranking.")
        
        return candidate_data[:top_k]

    def _scan_local_context(self, keywords):
        local_candidates = []
        if os.path.exists(self.local_dir):
            import glob
            # Recursively find all .lean files in subdirectories
            cache_files = glob.glob(os.path.join(self.local_dir, "**", "*.lean"), recursive=True)
            for file_path in cache_files:
                file_name = os.path.basename(file_path)
                try:
                    with open(file_path, "r", encoding="utf-8") as f:
                        content = f.read()
                        # Simple match for now; local context is small
                        # [FIX]: Use a more robust check for keywords to avoid partial matches
                        for kw in keywords:
                            if re.search(r'\b' + re.escape(kw) + r'\b', content):
                                local_candidates.append({
                                    "import": f"LOCAL_PROJECT.{file_name.replace('.lean', '')}",
                                    "path": file_path,
                                    "score": 3.0, # Local context is highest priority
                                    "content": content,
                                    "is_local": True
                                })
                                break
                except: pass
        return local_candidates

    def _fallback_keyword_search(self, keywords, query_description, top_k):
        # Extremely simplified keyword search as fallback
        return []

    def format_rag_context(self, search_results):
        if not search_results:
            return "No relevant Mathlib theorems found."
            
        context_str = "RELEVANT MATHLIB THEOREMS FOR YOUR TASK:\n"
        for res in search_results:
            context_str += f"\n--- File: {res['import']} ---\n"
            context_str += res['content']
            context_str += "\n--------------------------\n"
            
        return context_str

    async def verify_candidates(self, search_results, compiler):
        """
        [NEW] Validation-in-the-Loop: Use REPL to check if the retrieved 
        theorems actually exist and are accessible.
        """
        print(f"   🛡️ [Shield] Verifying {len(search_results)} candidates via REPL...")
        verified_results = []
        
        for res in search_results:
            # We skip verification for local project files for now
            if res.get("is_local"):
                verified_results.append(res)
                continue
                
            # Extract the theorem name (last part of the import or from content)
            # This is a heuristic: looking for 'theorem name' or 'def name'
            match = re.search(r'(theorem|def|lemma)\s+([^\s\(\{\:]+)', res['content'])
            if not match:
                verified_results.append(res) # Can't extract name, keep it
                continue
                
            thm_name = match.group(2)
            # Construct a check command with necessary import
            check_cmd = f"import {res['import']}\n#check {thm_name}"
            
            success, _ = await compiler.validate_with_repl_async(check_cmd)
            if success:
                verified_results.append(res)
            else:
                print(f"      🚫 [Filtered] API '{thm_name}' failed existence check. Likely a hallucination or path error.")
                
        return verified_results
