# A complete, isolated workflow example

This **new teaching fixture** exercises the production pack, build, review
request, freshness, and apply paths. It is not one of the 452 textbook tasks,
not retained historical evidence, and not a measurement of reviewer accuracy.

The source defines a rounded per-thousand observed frequency only on valid
counts. The initial code compiles while omitting its domain conditions. Adding
the conditions breaks the old caller; the final code supplies them explicitly.
The caller lives in the same Lean file to keep this example self-contained.
It demonstrates a call-interface migration, not atomic multi-task promotion.

Run from the repository root after installing the Python package and preparing
the pinned Lean REPL dependency:

```console
python tools/run_workflow_demo.py
```

The script preserves its isolated temporary run and prints the evidence path.
It never uses the live catalog, plans, corpus, or operational database. The
default is **recorded teaching-review replay**; no new model review occurs.

See [the runbook](../../docs/workflow_demo.md) for the real-review runner
interface, all stages, isolation guarantees, and limits.
