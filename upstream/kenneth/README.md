# Kenneth Chapter 1 upstream provenance

Kenneth's repository is a read-only upstream.  Nothing below is imported into
the active `ToyApollo` module graph automatically.

## Human-review anchor

The byte-exact file frozen at
`f81f1450/def_1_2a.lean` is the version Kenneth identified in the conversation
as his reviewed Definition 1.2 implementation.

- repository: `https://github.com/wkshum/ProbabilityTheory`
- commit: `f81f1450e49bd1bdf07cc123c5a221c7b39b0eb1`
- Git blob: `4c61a677f296ac11e923d06dbb267cf8da0b0ccd`
- byte size: `61677`

`tests/test_kenneth_upstream_provenance.py` checks this local copy using the Git
blob algorithm.  The file is provenance and must never be edited or imported.

## Later public snapshots

Kenneth published two later commits after the original anchor.  They are pinned
here by immutable commit and blob identifiers so future reconciliation does not
silently follow the moving `main` branch.

### Revised `def_1_2a`

- commit: `6e110e94d9219483cff90f04a8875d06029d2b0f`
- path: `ProbabilityTheory/chapter_01/def_1_2a.lean`
- Git blob: `9102c6bbcce2a347aef92c90e8f80eed583a81ad`
- byte size: `67343`

### Split Definition/Theorems layout

Commit `36c97725ab4341a4f97b59a674d0ce9b89209713` renamed the revised
`def_1_2a` to `def_1_2_backup` and published a smaller active definition plus
separate theorem files:

| Path under `ProbabilityTheory/chapter_01` | Git blob | Bytes |
| --- | --- | ---: |
| `def_1_2.lean` | `c0c6170923ac675281785fb940a44572c085c930` | 12870 |
| `def_1_2_backup.lean` | `a893af7a28279c7288a3e70cd7c0fb1ea4db14a9` | 45532 |
| `thm_1_2.lean` | `1b5beb48406a652ab5ab8f32286ff97c30bbef8f` | 45292 |
| `thm_1_2_4.lean` | `4c95f6366e29727e53af087649ce7fc6dc58196d` | 87066 |
| `thm_1_3.lean` | `b84b18fcd4602eaf2179fb74378893c97b5f57b3` | 9994 |

These later files are recorded for comparison, not promoted as additional
human-reviewed artifacts.  The conversation explicitly established human
review for Definition 1.2 only.

## Reconciliation decision

The active `ToyApollo/Output/def_1_2.lean` adopts Kenneth's useful finite
partition contract (`Fin (n + 1)` points, `Fin n` cells and finite sums) but is
not a whole-file copy.  The later upstream definition still makes both the
upper/lower limit and tagged convergence fields of a public integral witness.
That would regress the project's reviewed source-fidelity repair.

The canonical ToyApollo contract therefore remains:

- `RSIntegrable = DarbouxRS.RSIntegrableOnInterval`;
- integrability contains only the textbook upper/lower common-limit criterion;
- tagged convergence is derived by `taggedBridgeObligation` and
  `taggedCommonLimit_of_upperLowerCommonLimit`;
- later Kenneth commits are reconciled only by an explicit, reviewed commit.

