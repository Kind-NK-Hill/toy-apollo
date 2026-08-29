# Case studies

These eight case studies are small, immutable exports from ToyApollo's private
runtime evidence. They show why the project separates Lean compilation,
semantic review, diagnosis, downstream revalidation, and the final apply
decision.

They are not benchmark results. Full prompt packs contain source-corpus
mirrors, local paths, generated prompts, mutable status pointers, and redundant
artifacts; those remain private. Each public case keeps:

- sanitized compiling initial and final Lean slices;
- a structured verdict timeline;
- SHA-256 bindings to the retained private evidence;
- a concise account of the mathematical or proof-route defect.

[`cases.json`](cases.json) records the diversity policy and interview hook for
the complete set.

## Included cases

| Case | Distinct public question | Review history |
| --- | --- | --- |
| [`def_8_5`](def_8_5/) | Can code compile while defining total variation on the wrong domain? | 5 reviews; owner repair plus downstream migration |
| [`def_10_1`](def_10_1/) | Can a stronger review correctly invalidate an older pass? | 8 reviews; 40-target campaign scope |
| [`def_5_5`](def_5_5/) | Is a library alias enough to implement a source-facing definition? | 1 fail, 3 passes with advancing consumers |
| [`def_6_6`](def_6_6/) | Can an undefined integral be accidentally totalized? | pass → fail on same hash → repaired pass |
| [`ex_8_2_1`](ex_8_2_1/) | Is changing `ℝ × ℝ` to `ℕ × ℝ` a harmless encoding? | fail → owner contract decision → pass |
| [`ex_8_3_4`](ex_8_3_4/) | Does proving one feasible plan solve an optimization problem? | 2 different semantic failures before pass |
| [`thm_8_2`](thm_8_2/) | Does invoking the finished library theorem preserve a proof-bearing source route? | adapter-only fail followed by construction passes |
| [`thm_14_8`](thm_14_8/) | Can an explicit allowed exception later become a clean premise-free proof? | allowed exception → Interface fail → applied pass |

The set deliberately covers domain, carrier, quantifier, undefinedness,
adapter, proof-route, review-basis, public-premise, and downstream-fanout
failures. Seven of eight
cases involve mathematical statement or Interface drift; `thm_8_2` isolates
proof-route drift while keeping the theorem statement fixed.

## One-minute explanation

> ToyApollo treats Lean compilation as one gate, not as a semantic certificate.
> I preserved eight real repair histories in which compilable code used the
> wrong domain, carrier, quantifier structure, undefinedness convention, or
> proof route. Every public timeline binds its verdicts to candidate and review
> hashes, while CI compiles both the semantically rejected initial slice and the
> repaired final slice.

The defensible claim is that the repository makes semantic failures and repair
decisions inspectable. The selected cases do not estimate model accuracy or
prove that semantic review is infallible.

## Inspect locally

From the repository root:

```powershell
Get-ChildItem .\examples\case-studies -Directory | ForEach-Object {
    lake env lean (Join-Path $_.FullName 'initial.lean')
    if ($LASTEXITCODE -ne 0) { throw "initial snapshot failed: $($_.Name)" }
    lake env lean (Join-Path $_.FullName 'final.lean')
    if ($LASTEXITCODE -ne 0) { throw "final snapshot failed: $($_.Name)" }
}
python .\tools\check_case_studies.py
```

Both slices in every case are expected to compile. Compilation is intentionally
insufficient to decide the semantic verdict; read the adjacent timeline.

For the authority model, see
[`docs/phase2/artifacts.md`](../../docs/phase2/artifacts.md) and
[`docs/phase2/review_criteria.md`](../../docs/phase2/review_criteria.md).
