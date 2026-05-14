def build_aristotle_prompt(task_id: str) -> str:
    return (
        "You are working on a Lean project with one primary target file that still contains `sorry`.\n"
        f"Target task id: {task_id}.\n\n"
        "Instructions:\n"
        "1. Complete the target task by filling the remaining `sorry` in the uploaded project.\n"
        "2. Reuse uploaded local dependencies from `ToyApollo/Output/*.lean` whenever applicable.\n"
        "3. `hard dependencies` and `soft imports` are both mandatory project dependencies once uploaded.\n"
        "4. Do not redefine or duplicate any definition, theorem, lemma, structure, or notation already provided by uploaded local dependencies.\n"
        "5. Minimize edits outside the target file; only change other files if a direct compile blocker forces it.\n"
        "6. Preserve the intended mathematics and avoid unrelated refactors or stylistic rewrites.\n"
        "7. The final result must leave the uploaded Lean project in a compilable state.\n"
    )
