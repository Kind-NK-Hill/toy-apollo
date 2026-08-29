import os
import glob
from src.block_id_naming import canonicalize_block_id, parent_block_id

class ContextManager:
    """
    上下文管理器 (Global Context Pool)
    负责存储已生成的 Lean 代码，支持从本地缓存中恢复历史记忆，
    并为当前任务提取最精简、最相关的历史代码作为 Context。
    """
    def __init__(self, output_dir="output_lean_files"):
        self.code_store = {}
        self.failed_statements = {} # Stores block_id -> theorem/def signature with sorry
        self.output_dir = output_dir
        self._load_existing_cache()

    def _load_existing_cache(self):
        """在启动时，扫描 output 目录，将已成功的代码加载到内存池中"""
        if not os.path.exists(self.output_dir):
            return

        # 查找所有 .lean 文件 (递归)
        cache_files = glob.glob(os.path.join(self.output_dir, "**", "*.lean"), recursive=True)
        loaded_count = 0

        for file_path in cache_files:
            filename = os.path.basename(file_path)
            # 文件名为 block_id.lean
            block_id = canonicalize_block_id(filename.replace(".lean", ""))
            try:
                with open(file_path, "r", encoding="utf-8") as f:
                    self.code_store[block_id] = f.read()
                    loaded_count += 1
            except Exception as e:
                print(f"   ⚠️ [ContextManager] Failed to load cache {filename}: {e}")

        if loaded_count > 0:
            print(f"   🧠 [ContextManager] Successfully loaded {loaded_count} cached blocks into Global Pool.")

    def add_success(self, block_id, lean_code):
        """记录新成功的代码"""
        block_id = canonicalize_block_id(block_id)
        self.code_store[block_id] = lean_code
        # Clear from failed statements if it now succeeded
        self.failed_statements.pop(block_id, None)
        print(f"   📦 [ContextManager] Saved code for block: {block_id}")

    def add_failed_statement(self, block_id, signature):
        """记录证明失败但签名可用的任务"""
        block_id = canonicalize_block_id(block_id)
        self.failed_statements[block_id] = signature
        print(f"   📓 [ContextManager] Recorded failed statement for block: {block_id}")

    def _get_transitive_dependencies(self, block_id, all_blocks_dict):
        """递归获取所有的前置依赖（传递闭包），并支持分解感知"""
        block_id = canonicalize_block_id(block_id)
        deps = set()
        if block_id not in all_blocks_dict:
            # [NEW] Decomposition Awareness: If the block_id is missing but exists as a prefix in code_store,
            # it means this was a decomposed parent.
            for stored_id in self.code_store.keys():
                if stored_id.startswith(f"{block_id}__") or parent_block_id(stored_id) == block_id:
                    deps.add(stored_id)
            return deps

        direct_deps = all_blocks_dict[block_id].get('dependencies', [])
        for dep in direct_deps:
            dep = canonicalize_block_id(dep)
            if dep not in deps:
                # If the dependency exists directly, add it
                if dep in self.code_store:
                    deps.add(dep)
                else:
                    # If it doesn't exist directly, it might be a decomposed parent
                    children = [sid for sid in self.code_store.keys() if sid.startswith(f"{dep}_")]
                    if not children:
                        children = [sid for sid in self.code_store.keys() if sid.startswith(f"{dep}__")]
                    if children:
                        deps.update(children)
                    else:
                        # Fallback: still treat it as a dependency to trigger warnings or deep search
                        deps.add(dep)

                # Recursive call
                deps.update(self._get_transitive_dependencies(dep, all_blocks_dict))
        return deps

    def get_context_for(self, current_task, all_tasks_list):
        """为当前任务生成精简的 Lean Context"""
        all_blocks_dict = {}
        for task in all_tasks_list:
            canonical_id = canonicalize_block_id(task.get('block_id', ''))
            if not canonical_id:
                continue
            canonical_task = dict(task)
            canonical_task['block_id'] = canonical_id
            canonical_task['dependencies'] = [
                canonicalize_block_id(dep)
                for dep in task.get('dependencies', [])
                if canonicalize_block_id(dep)
            ]
            all_blocks_dict[canonical_id] = canonical_task

        required_deps = self._get_transitive_dependencies(current_task['block_id'], all_blocks_dict)

        if not required_deps:
            return ""

        ordered_context_codes = []
        # 按照任务列表的顺序提取上下文，保证 Lean 编译的自上而下顺序
        for task in all_tasks_list:
            b_id = canonicalize_block_id(task['block_id'])
            if b_id in required_deps:
                if b_id in self.code_store:
                    ordered_context_codes.append(f"-- Context from: {task['title']}\n{self.code_store[b_id]}")
                else:
                    print(f"   ⚠️ [ContextManager Warning] Dependency '{b_id}' is required but its code is missing/failed.")

        # 额外检查：如果依赖的 block_id 不在当前文件的 task_list 中，但在全局缓存中
        # 这处理了跨文件依赖的情况（例如 chap4 依赖 chap3 的定义）
        for b_id in required_deps:
            if b_id not in all_blocks_dict and b_id in self.code_store:
                 ordered_context_codes.insert(0, f"-- External Context: {b_id}\n{self.code_store[b_id]}")

        final_context = "\n\n".join(ordered_context_codes)
        if final_context:
            print(f"   🧩 [ContextManager] Assembled context from {len(ordered_context_codes)} dependencies.")

        return final_context
