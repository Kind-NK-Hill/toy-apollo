# Chapter 1 Kenneth intake and integration matrix

Upstream is read-only `wkshum/ProbabilityTheory` `main` at
`2b86c183a7da2bd1af77a99870b93197067d7558`, tree
`95da03e39418ce2435f4f161a36d663411f5e87b`. The commit, tree, blobs and byte
sizes are fixed in `upstream/kenneth/2b86c183/manifest.json`. A fresh
`git ls-remote` on 2026-07-11 returned the same commit.

This matrix records the source-facing merge decision. Kenneth blobs are never
edited. `K-support` means that the reviewed proof body is retained under a
namespace in a ToyApollo support module, with only import, namespace and the
documented source-only witness migration applied.

| Kenneth file/blob | ToyApollo canonical/support | Review scope and interface difference | Decision / downstream impact |
| --- | --- | --- | --- |
| `Main.lean` / `1a9cece` | all Chapter 1 task/support modules | Kenneth omitted `thm_1_1` and item 4; ToyApollo has the full active graph | ToyApollo active surface; all modules are built below |
| `def_1_1.lean` / `e25fe9f` | `def_1_1.lean` | Same singular-law definitions; ToyApollo has source-facing measure typing | ToyApollo; no downstream change |
| `def_1_2.lean` / `e8608eb` | `def_1_2.lean` | Protected `Fin (n+1)` points, `Fin n` cells/tags and `Finset.univ` sums are present. Kenneth exported a source+tagged witness; ToyApollo exports only upper/lower common limit and derives tagged convergence | Semantic merge already present; preserve ToyApollo public contract |
| `def_1_2_backup.lean` / `a893af7` | `def_1_2.lean`, `rs_stieltjes_darboux_support.lean` | Backup algebra/order lemmas are already present in canonical/support form | ToyApollo consolidation; no duplicate public API |
| `def_1_3.lean` / `a9e6db1` | `def_1_3.lean`, `def_1_3_kenneth_finite_support.lean`, `thm_1_3_kenneth_support.lean` | Kenneth finite-interval public CDF accepted arbitrary monotone data. ToyApollo main interface uses a Stieltjes measure and whole-line finite moments. Kenneth variance nonnegativity, zero integrator, finite integrator sum, one-jump identity, finite discrete expectation and density proofs were absent before this integration | K-support proof bodies imported by canonical `def_1_3`; main interface remains probability/source-facing |
| `def_1_4.lean` / `2dba3c8` | `def_1_4.lean` | Same improper filter and convergence/value package; Kenneth totalized missing truncations with `else 0` | Semantic merge already present: proof-carrying truncation, no totalization |
| `thm_1_1.lean` / `c13013d` and eight `thm_1_1_*` blobs | `thm_1_1.lean` and eleven `thm_1_1_*` support modules | Kenneth chain was inactive and partly Nat/stale; ToyApollo contains its migrated Fin refinement/oscillation/common-limit route | ToyApollo Fin migration; all affected imports built |
| `thm_1_2.lean` / `f69a594` | `def_1_2.lean`, `thm_1_2.lean` | Kenneth items 1–3 proof algebra is retained in the canonical Fin laws; current item 4 uses the migrated Fin proof and exposes the known source-statement boundary | Semantic consolidation; no Nat API restored |
| `thm_1_2_4.lean` / `4c95f63` | `thm_1_2.lean` | Kenneth file was inactive and failed against Fin; its insertion/gluing proof material is present in the migrated canonical file | ToyApollo migrated proof; downstream remains isolated |
| `thm_1_3.lean` / `055754b` | `thm_1_3.lean`, `thm_1_3_kenneth_support.lean` | Exact reviewed additivity and scalar-integrator proof bodies are retained; witness constructors are migrated from source+tagged to source-only | K-support plus concise canonical theorem; imported by Definition 1.3 support |
| `thm_1_4.lean` / `6b4918f` and backup `febe7d6` | `thm_1_4.lean` | Fin/MVT/tagged-sum/interval-integral spine is retained. Public monotonicity is corrected from global `Monotone` to textbook `MonotoneOn (Icc a b)` | ToyApollo source-facing repair; density proofs pass the restricted monotonicity |

Kenneth has no Chapter 1 example or problem files. Every ToyApollo
`ex_1_*`/`prob_1_*` module was therefore checked for upstream correspondence
through its imports and source span rather than a same-name blob; none has a
new Kenneth revision to merge. Their direct Chapter 1 RS consumers build
against the merged canonical graph.

## Integration invariants

- No frozen upstream file was edited.
- No Chapter 2–4 source was imported or changed.
- `RSIntegrable` remains the textbook upper/lower common-limit predicate.
- `taggedCommonLimit_of_upperLowerCommonLimit` remains a derived sandwich theorem.
- Improper truncation remains proof-carrying; no `else 0` enters the result.
- Kenneth finite Definition 1.3 and Theorem 1.3 proof bodies are now actual
  compiled dependencies of canonical `def_1_3`, not reference-only prose.
