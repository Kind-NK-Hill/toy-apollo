# Case studies

These case studies are small, immutable exports from ToyApollo's private
runtime evidence. They show why the project separates Lean compilation from
semantic review and from the final apply decision.

They are not a benchmark result. The full prompt packs contain local paths,
source-corpus mirrors, mutable status pointers, and redundant generated files;
those remain in the private evidence plane. Each public case keeps only:

- a sanitized initial and final Lean subject;
- a structured verdict timeline;
- hashes of the private evidence from which the case was curated;
- an explanation of what the review mechanism caught.

## Included cases

| Case | Public question | Evidence shown |
| --- | --- | --- |
| [`def_8_5`](def_8_5/) | Can code compile while defining total variation on the wrong domain? | 4 build candidates, 5 semantic-review results, two distinct failure classes |
| [`def_10_1`](def_10_1/) | Can an earlier pass be invalidated when a stricter review exposes a high-fanout interface defect? | 8 semantic-review results and a 40-target fanout inspection |

## Inspect locally

From the repository root:

```powershell
lake env lean .\examples\case-studies\def_8_5\initial.lean
lake env lean .\examples\case-studies\def_8_5\final.lean
lake env lean .\examples\case-studies\def_10_1\initial.lean
lake env lean .\examples\case-studies\def_10_1\final.lean
```

Both the initial and final subjects are expected to compile. The semantic
defect is therefore invisible to the build gate alone. Read each
`review-timeline.json` next to the code to see the independent review and
repair sequence.

For the authority model behind these files, see
[`docs/phase2/artifacts.md`](../../docs/phase2/artifacts.md) and
[`docs/phase2/review_criteria.md`](../../docs/phase2/review_criteria.md).
