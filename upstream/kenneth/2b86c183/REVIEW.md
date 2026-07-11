# Review of Kenneth Chapter 1 baseline `2b86c183`

This is a read-only review of Kenneth's public repository at the exact commit
recorded in `manifest.json`.  It does not modify Kenneth's repository and does
not replace an official ToyApollo `review-apply` result.

## Overall verdict

`FAIL` as a complete Chapter 1 landing.  Several proof bodies are valuable and
must be preserved, but the active surface is incomplete and three public
contracts are semantically stronger or less guarded than the textbook route.

| File/task | Verdict | Decision |
| --- | --- | --- |
| `Main.lean` | `FAIL` | It compiles only the selected active surface; `thm_1_1` is commented out and `thm_1_2_4` is never imported. |
| `def_1_2.lean` | `FAIL / public_premise` | Preserve the Fin partition core. Replace only the public double-witness layer with the source-only upper/lower contract. |
| `def_1_3.lean` | `FAIL / partial_direct` | Preserve the finite atomic and finite density proof bodies as support. Repair the main interface to use a genuine probability CDF and the whole-line guarded improper RS definition. |
| `def_1_4.lean` | `FAIL / totalization` | Preserve `improperRSFilter` and existential/value packaging. Replace `else 0` truncations with the proof-carrying contract already implemented in ToyApollo. |
| `thm_1_1*.lean` | `NOT_ACTIVE`, independent build `FAIL` | Migrate the old Nat/namespace consumers to the active Fin API before review. |
| `thm_1_2.lean` | `PASS` for items 1--3 | Preserve this file as reviewed partial theorem material. It does not complete Theorem 1.2 by itself. |
| `thm_1_2_4.lean` | `NOT_ACTIVE`, independent build `FAIL` | It still uses the old Nat partition API and reaches many elaboration errors against the Fin definition. Use the already migrated ToyApollo item-4 route. |
| `thm_1_3.lean` | `PASS` | Preserve the exact proof unless a later dependency review finds a real incompatibility. |
| `thm_1_4.lean` | `FAIL / strengthened premise` | Preserve the Fin/MVT/integral proof body. Repair the public chain from global `Monotone alpha` to textbook `MonotoneOn alpha (Icc a b)`. |

## Blocking findings

### Definition 1.2

The source defines RS integrability by convergence of the upper and lower sums
to the same value.  The candidate already contains the faithful predicate
`RSIntegrableOnInterval`, but its exported `RSIntegrable` instead requires an
`RSIntegralWitness` with both `source_limit` and `tagged_limit`.  Tagged
convergence is a theorem derived by the sandwich argument, not an additional
public construction premise.

The following content is protected and should be reused unchanged where
possible: the Fin partition, `Fin (n + 1)` points, `Fin n` cells and tags,
`StrictMono`, upper/lower sums, `UpperLowerCommonLimit`, uniform partitions and
tagged-limit uniqueness.

### Definition 1.3

The candidate proves useful finite-interval identities, but its main
`cdfExpectation` and `cdfVariance` accept an arbitrary real function with a
finite-interval RS witness.  They do not bind the integrator to a probability
law/CDF and do not use Definition 1.4 for the whole real line.  Its
`discreteCDF` does not require total mass one, and the discrete theorem retains
a redundant task-shaped `h_int` premise.

The single-jump calculation, finite integrator sum, finite atomic expectation
formula, finite density formula through Theorem 1.4, and finite variance
nonnegativity proof are protected as support material.

### Definition 1.4

`rsTruncIntegral` returns zero when finite RS integrability is unavailable.  The
convergence predicate is therefore stated over a totalized public function.
The double-limit filter and the finite-real existential/value packaging are
correct, but truncation values must carry an explicit `RSIntegrable` witness.

### Theorem surface

`Main.lean` does not establish a complete Chapter 1 build.  Theorem 1.1 is
commented out.  Theorem 1.2 item 4 lives in an unimported file that still uses
the old Nat-indexed partition API.  Items 1--3 and Theorem 1.3 are buildable and
mathematically usable.  Theorem 1.4 has a strong proof body, but its public
signature unnecessarily strengthens interval monotonicity to global
monotonicity.

## Build evidence and limits

- Independent reviewers compiled `def_1_2.lean` standalone and the active
  theorem files under Lean/Mathlib 4.31.
- The selected `Main.lean` surface compiled in the reviewer check.
- Independent compilation of the excluded Theorem 1.1 chain failed at its old
  namespace/Nat interface; the excluded item-4 file produced extensive Fin/Nat
  elaboration failures.
- A cold full `lake build` in the detached verification worktree spent the
  allotted run preparing/building Mathlib dependencies and timed out without a
  canonical project result.  That mechanism timeout is not counted as a
  mathematical failure and does not override the narrower build findings.

## Protection rule after review

The exact upstream blobs remain immutable provenance.  A `PASS` file is not to
be edited without a later concrete failure.  For a `FAIL` file, only the
blocking public layer identified above is authorized for repair; passing proof
bodies and Fin constructions remain protected.
