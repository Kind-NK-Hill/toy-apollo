import os
import json
import asyncio
import subprocess
import tarfile
import shutil
import aristotlelib
from pathlib import Path
from src.config import ARISTOTLE_API_KEY

class AristotlePhase3Manager:
    def __init__(self, api_key=None):
        self.api_key = api_key or ARISTOTLE_API_KEY or os.getenv("ARISTOTLE_API_KEY")
        if not self.api_key:
            raise ValueError("❌ ARISTOTLE_API_KEY not found in environment variables.")
        aristotlelib.set_api_key(self.api_key)

    async def run_offload(self, task_id, staging_dir, prompt="Fill in all the sorries in this project"):
        """
        [CORE] 执行全生命周期卸载：提交 -> 等待 -> 收割 -> 集成
        """
        print(f"\n🚀 [Phase 3] Initiating Cloud Offload for: {task_id}")
        staging_path = Path(staging_dir)
        
        try:
            # 1. 提交项目镜像 (SDK)
            print(f"   📤 Uploading project from {staging_path}...")
            project = await aristotlelib.Project.create_from_directory(
                prompt=prompt,
                project_dir=str(staging_path)
            )
            print(f"   📡 Job dispatched. Project ID: {project.project_id}")

            # 2. 异步等待完成 (SDK)
            print(f"   ⏳ Waiting for Aristotle to solve (MCGS in progress)...")
            # 注意：这可能需要 1-10 分钟
            await project.wait_for_completion()
            print(f"   ✅ Aristotle finished task: {task_id}")

            # 3. 物理收割成果 (CLI Bridge)
            # 将结果存入专用存档目录：aristotle_archives/[task_id]/
            archive_root = Path("aristotle_archives") / task_id
            extracted_dir = archive_root / "extracted"
            os.makedirs(extracted_dir, exist_ok=True)
            
            tar_name = f"{project.project_id}-aristotle.tar.gz"
            tar_path = archive_root / tar_name
            
            print(f"   📥 Harvesting result to {tar_path}...")
            cli_cmd = [
                "aristotle", "result", str(project.project_id),
                "--destination", str(tar_path),
                "--wait"
            ]
            
            proc = subprocess.run(cli_cmd, capture_output=True, text=True)
            if proc.returncode != 0:
                print(f"   ❌ CLI Error: {proc.stderr}")
                return False

            # [FIX] Manually move the file if it ended up in the current directory
            local_tar = Path(tar_name)
            if local_tar.exists() and not tar_path.exists():
                shutil.move(str(local_tar), str(tar_path))

            # 4. 解压并集成回本地
            print(f"   📦 Extracting project archive to {extracted_dir}...")
            with tarfile.open(tar_path, "r:gz") as tar:
                tar.extractall(path=extracted_dir)
            
            # 5. 精准定位并提取补全后的文件
            completed_file = None
            # 优先在解压后的 extracted 目录中寻找
            for p in extracted_dir.rglob(f"{task_id}.lean"):
                with open(p, "r", encoding="utf-8") as f:
                    if "sorry" not in f.read():
                        completed_file = p
                        break

            if completed_file:
                final_dest = Path("output_lean_files/general") / f"{task_id}.lean"
                shutil.copy(completed_file, final_dest)
                print(f"   ✨ SUCCESS! Verified proof saved to: {final_dest}")
                
                # 同步到编译镜像区
                shutil.copy(completed_file, Path("ToyApollo/Output") / f"{task_id}.lean")
                return True
            else:
                print(f"   ❌ Critical: Could not find a version of {task_id}.lean without 'sorry' in the archive.")
                return False

        except Exception as e:
            print(f"   💥 Phase 3 Error for {task_id}: {e}")
            return False
        finally:
            # 清理临时压缩包
            if (staging_path / f"{task_id}_result.tar.gz").exists():
                os.remove(staging_path / f"{task_id}_result.tar.gz")

async def main():
    # 简单的测试运行
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--task_id", type=str, required=True)
    parser.add_argument("--dir", type=str, required=True, help="Path to the direct_xxx/task_id folder")
    args = parser.parse_args()

    manager = AristotlePhase3Manager()
    success = await manager.run_offload(args.task_id, args.dir)
    if success:
        print(f"\n🎉 Task {args.task_id} successfully rescued by Aristotle!")
    else:
        print(f"\n❌ Task {args.task_id} offload failed.")

if __name__ == "__main__":
    asyncio.run(main())
