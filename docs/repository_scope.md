# Repository and publication scope

ProbabilityTheoryFormalization publishes its runtime, Lean output, tests,
documentation and selected evidence. Complete source material and operational
history remain in the owner's separate workspace. Ignored or unpublished files
remain protected evidence, not deletion candidates.

## Public and retained material

| Material | Public release | Retained workspace |
| --- | --- | --- |
| `src/formalization_engine/`, tools and tests | Reusable code | Development and historical revisions |
| `ProbabilityTheory/` | Executable Lean with source-derived block prose removed | Original source-facing comments and evidence |
| `manifest_by_chapter.csv` | Build lookup and published content hashes only | Full source catalog and historical metadata |
| `inputs/`, `plans/`, catalog policies, `upstream/` | Omitted | Complete source and provenance |
| Operational database, prompt packs, logs, live receipts | Omitted | Mutable state and original evidence |
| Eight historical case exports | Fixed Lean slices and sanitized timelines | Full original review/build records |
| Complete workflow demonstration | Newly authored input and teaching review | Each user's separately generated isolated run |
| Review identity/comparison pilots | Code, protocols and small demonstration inputs | Prospective runs and independent adjudications when collected |

The public manifest has five columns: `basename`, `file_path`, `module_name`,
`chapter`, `sha256`. It enables build lookup and integrity checks; it carries no
review verdict, catalog-completion status or authority binding. Full-workspace
`formalize state validate` needs the omitted catalog and evidence.

## Lean publication transform

The exporter reads an explicit committed source revision. For each corpus file
it removes block-comment prose while retaining executable Lean and a standard
source-omission notice. It refuses a transform that changes the normalized
executable text. It does not rewrite the private source tree.

`data/publication/corpus_map.json` records the source and published SHA-256 of
each normalized UTF-8/LF file, the source commit, and combined fingerprints.
`data/publication/release_manifest.json` records the release inventory and
transformations. `COORDINATION_PROVENANCE.md` publishes only the original corpus
and manifest fingerprints. These are content provenance, not semantic review.

## Reproduce a release export

From the maintainer's complete source repository, after committing the intended
release changes:

```powershell
python tools/export_public_release.py --source-ref HEAD --destination C:\exports\probability-v0.2.0
python tools/check_public_release.py --root C:\exports\probability-v0.2.0 --export-directory
```

The destination must be absent or empty and outside the source repository.
Uncommitted changes are not exported. Existing exports are preserved; the tool
does not remove directories. Validate the exported tree and its builds before
committing it onto the existing public branch.

The public build manifest is already transformed, so a public clone is not a
substitute for the private source input to this exporter. It can independently
verify the released files with `python tools/check_public_release.py` and build
them without the original private evidence.

## Historical cases and the runnable demonstration

The [eight cases](../examples/case-studies/README.md) are selected explanations,
not a random sample or a performance benchmark. Their immutable Lean/JSON files
retain the original public hashes and timelines. The diversity requirements in
`cases.json` describe coverage of failure mechanisms, not statistical sampling.
Current corpus links may point to later maintained implementations; they are
distinct from the fixed initial/final case snapshots.

The [complete workflow demonstration](workflow_demo.md) uses production APIs,
Lean compilation and a new isolated database. Its recorded review replay is
teaching evidence. It must not be imported into the textbook catalog or described
as a new independent model review. The optional external-reviewer path performs
a fresh call and records its actual identity and outcome.

The [identity pilot](review_basis_pilot.md) checks a proposed separation of
identity dimensions. The [prospective comparison](review_comparison_pilot.md)
provides paired requests and scoring with unresolved adjudications; neither
establishes improved model quality from its synthetic checks.

## Publication history

The existing public history was created as a sanitized projection of development
history. That already published history remains intact. The v0.2 release is a
new exported tree committed normally on top of public `main`; private Git history
is not merged, pushed, or rewritten into the public repository.

Removing a private file in a later commit does not erase it from earlier Git
objects. Keep the source/research remote private and export only the reviewed
public tree. Retained source and published fingerprints make the transform
inspectable without exposing the private history or mutable operational state.
