import os
import json
import asyncio
import subprocess
import tarfile
import shutil
import aristotlelib
from pathlib import Path
from src.config import ARISTOTLE_API_KEY
from src.aristotle_prompt import build_aristotle_prompt
from src.toy_apollo.core.settings import get_settings

class AristotlePhase3Manager:
    def __init__(self, api_key=None):
        self.api_key = api_key or ARISTOTLE_API_KEY or os.getenv("ARISTOTLE_API_KEY")
        if not self.api_key:
            raise ValueError("❌ ARISTOTLE_API_KEY not found in environment variables.")
        aristotlelib.set_api_key(self.api_key)
        self.settings = get_settings()

    def _verify_harvested_file(self, task_id: str, candidate_file: Path, archive_root: Path) -> tuple[bool, str]:
        """
        Keep Aristotle raw output in archives first. Promote to active outputs only if local build passes.
        On verification failure, restore the previous active file (if any) and keep only the archived raw copy.
        """
        toy_output = self.settings.toyapollo_output_dir
        general_output = self.settings.output_lean_files_dir / "general"
        toy_output.mkdir(parents=True, exist_ok=True)
        general_output.mkdir(parents=True, exist_ok=True)

        active_path = toy_output / f"{task_id}.lean"
        general_path = general_output / f"{task_id}.lean"
        previous_active = active_path.read_text(encoding="utf-8") if active_path.exists() else None

        if candidate_file.resolve() != active_path.resolve():
            shutil.copy(candidate_file, active_path)
        proc = subprocess.run(
            ["lake", "build", f"ToyApollo.Output.{task_id}"],
            capture_output=True,
            text=True,
            cwd=str(self.settings.runtime_root),
        )
        build_output = ((proc.stdout or "") + "\n" + (proc.stderr or "")).strip()

        verify_dir = archive_root / "verification"
        verify_dir.mkdir(parents=True, exist_ok=True)
        (verify_dir / f"{task_id}_phase3_lake_build.log").write_text(build_output, encoding="utf-8")

        if proc.returncode == 0:
            shutil.copy(candidate_file, general_path)
            verified_dir = archive_root / "verified"
            verified_dir.mkdir(parents=True, exist_ok=True)
            shutil.copy(candidate_file, verified_dir / f"{task_id}.lean")
            return True, ""

        if previous_active is None:
            try:
                active_path.unlink()
            except FileNotFoundError:
                pass
        else:
            active_path.write_text(previous_active, encoding="utf-8")

        return False, build_output or "phase3_local_lake_build_failed"

    def _write_upload_manifest(self, task_id: str, staging_path: Path, prompt: str) -> None:
        dependency_manifest_path = staging_path / "dependency_manifest.json"
        dependency_manifest: dict = {}
        if dependency_manifest_path.exists():
            try:
                dependency_manifest = json.loads(dependency_manifest_path.read_text(encoding="utf-8"))
            except Exception:
                dependency_manifest = {}

        file_list: list[str] = []
        for file_path in sorted(staging_path.rglob("*")):
            if file_path.is_file():
                file_list.append(str(file_path.relative_to(staging_path)).replace("\\", "/"))

        upload_manifest = {
            "task_id": task_id,
            "prompt": prompt,
            "task_type": dependency_manifest.get("task_type", ""),
            "main_task_file": f"ToyApollo/Output/{task_id}.lean",
            "hard_dependencies": dependency_manifest.get("hard_dependencies", []),
            "soft_imports": dependency_manifest.get("soft_imports", []),
            "final_import_union": dependency_manifest.get("final_import_union", []),
            "uploaded_files": file_list,
        }
        (staging_path / "upload_manifest.json").write_text(
            json.dumps(upload_manifest, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )

    def _build_upload_tar(self, task_id: str, staging_path: Path, prompt: str) -> Path:
        upload_tar_path = staging_path.parent / f"{task_id}_upload.tar.gz"
        if upload_tar_path.exists():
            upload_tar_path.unlink()
        self._write_upload_manifest(str(task_id), staging_path, prompt)
        with tarfile.open(upload_tar_path, "w:gz") as tar:
            for dirpath, _, filenames in os.walk(staging_path):
                for filename in filenames:
                    file_path = Path(dirpath) / filename
                    rel_path = file_path.relative_to(staging_path)
                    tar.add(file_path, arcname=str(rel_path))
        return upload_tar_path

    async def submit_offload(self, task_id, staging_dir, prompt=None):
        """
        Submit a task to Aristotle and return as soon as the cloud job id is available.
        """
        print(f"\n🚀 [Phase 3] Submitting Cloud Offload for: {task_id}")
        staging_path = Path(staging_dir)
        project_id = ""
        prompt = prompt or build_aristotle_prompt(str(task_id))
        upload_tar_path: Path | None = None
        
        try:
            print(f"   📤 Uploading project from {staging_path}...")
            upload_tar_path = self._build_upload_tar(str(task_id), staging_path, prompt)

            project = await aristotlelib.Project.create(
                prompt=prompt,
                tar_file_path=upload_tar_path,
                public_file_path=f"{task_id}.tar.gz",
            )
            project_id = str(project.project_id)
            print(f"   📡 Job dispatched. Project ID: {project_id}")
            return {"success": True, "cloud_project_id": project_id, "error": ""}
        except Exception as e:
            print(f"   💥 Phase 3 submit error for {task_id}: {e}")
            return {"success": False, "cloud_project_id": project_id, "error": str(e)}
        finally:
            if upload_tar_path is not None:
                try:
                    if upload_tar_path.exists():
                        os.remove(upload_tar_path)
                except Exception as cleanup_error:
                    try:
                        with open(upload_tar_path, "wb"):
                            pass
                        print(f"   ⚠️ Delete denied; truncated instead: {upload_tar_path}")
                    except Exception:
                        print(f"   ⚠️ Cleanup skipped for {upload_tar_path}: {cleanup_error}")

    async def harvest_offload(self, task_id, project_id):
        """
        Wait for an already-submitted Aristotle project, then harvest and locally verify it.
        """
        print(f"\n🚜 [Phase 3] Harvesting Cloud Result for: {task_id}")
        project_id = str(project_id or "").strip()
        if not project_id:
            return {"success": False, "cloud_project_id": "", "error": "missing_cloud_project_id"}

        try:
            archive_root = self.settings.aristotle_archives_dir / task_id
            extracted_dir = archive_root / "extracted"
            os.makedirs(extracted_dir, exist_ok=True)
            
            tar_name = f"{project_id}-aristotle.tar.gz"
            tar_path = archive_root / tar_name
            
            print(f"   📥 Harvesting result to {tar_path}...")
            cli_cmd = [
                "aristotle", "result", project_id,
                "--destination", str(tar_path),
                "--wait"
            ]
            
            proc = subprocess.run(cli_cmd, capture_output=True, text=True)
            if proc.returncode != 0:
                err = f"aristotle_result_cli_failed: {proc.stderr.strip()}"
                print(f"   ❌ CLI Error: {proc.stderr}")
                return {"success": False, "cloud_project_id": project_id, "error": err}

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
                raw_dir = archive_root / "raw"
                raw_dir.mkdir(parents=True, exist_ok=True)
                raw_dest = raw_dir / f"{task_id}.lean"
                shutil.copy(completed_file, raw_dest)
                print(f"   📁 Raw Aristotle result saved to: {raw_dest}")

                verified, verify_error = self._verify_harvested_file(task_id, raw_dest, archive_root)
                if verified:
                    final_dest = self.settings.output_lean_files_dir / "general" / f"{task_id}.lean"
                    print(f"   ✨ SUCCESS! Local build passed. Promoted to active output: {final_dest}")
                    return {"success": True, "cloud_project_id": project_id, "error": ""}

                err = f"phase3_local_lake_build_failed:{verify_error}"
                print(f"   ❌ Local build failed after harvest. Active output was not kept. Raw backup only: {raw_dest}")
                return {"success": False, "cloud_project_id": project_id, "error": err}
            else:
                err = f"harvested_file_not_found_without_sorry:{task_id}"
                print(f"   ❌ Critical: Could not find a version of {task_id}.lean without 'sorry' in the archive.")
                return {"success": False, "cloud_project_id": project_id, "error": err}

        except Exception as e:
            print(f"   💥 Phase 3 harvest error for {task_id}: {e}")
            return {"success": False, "cloud_project_id": project_id, "error": str(e)}

    async def run_offload(self, task_id, staging_dir, prompt=None):
        """
        Backward-compatible helper: submit first, then harvest the same task immediately.
        """
        submit_result = await self.submit_offload(task_id, staging_dir, prompt=prompt)
        if not bool(submit_result.get("success")):
            return submit_result
        return await self.harvest_offload(task_id, submit_result.get("cloud_project_id", ""))

async def main():
    # 简单的测试运行
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--task_id", type=str, required=True)
    parser.add_argument("--dir", type=str, required=True, help="Path to the direct_xxx/task_id folder")
    args = parser.parse_args()

    manager = AristotlePhase3Manager()
    result = await manager.run_offload(args.task_id, args.dir)
    success = bool(result.get("success")) if isinstance(result, dict) else bool(result)
    if success:
        print(f"\n🎉 Task {args.task_id} successfully rescued by Aristotle!")
    else:
        print(f"\n❌ Task {args.task_id} offload failed.")

if __name__ == "__main__":
    asyncio.run(main())
