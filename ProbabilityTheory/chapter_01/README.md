# Chapter 1 — Reading Guide

This folder holds the complete reviewed Chapter 1 scope in the same package
layout used by Kenneth's repository: Definitions 1.1–1.4, Theorems 1.1–1.4,
Examples 1.2.1–1.3.2, Problems 1.1–1.10, and the support modules they actually
import. Theorem 1.1 is split into internal layers named
`thm_1_1_*`; those support files sit beside the public entry because Lean module
paths now match the PR target directly.

## Theorem 1.1 — where to look

| File | What to read it for |
|---|---|
| [`thm_1_1.lean`](thm_1_1.lean) | **Theorem 1.1 itself** — the textbook statement (in the docstring) and the final `theorem thm_1_1`. Start here. |
| [`def_1_2.lean`](def_1_2.lean) | Definition 1.2, the Riemann–Stieltjes integrability predicate that Theorem 1.1 concludes. |
| `thm_1_1_*.lean` | Internal proof layers (Darboux sums, oscillation, refinement, finite-discontinuity assembly). These are **not** separate textbook theorems. |

Opening `thm_1_1.lean` now shows the theorem directly:

```lean
theorem thm_1_1
    {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : Monotone α)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont : ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) :
    RSIntegrable f α a b
```

which reads: if `f` is bounded on `[a,b]` with only finitely many
discontinuities (`hDiscFinite`), and the non-decreasing integrator `α`
(`hα_mono`) is continuous at each discontinuity of `f` (`hαCont`), then
`f ∈ 𝓡(α)`. This matches Theorem 1.1 of the book. (`α` is non-decreasing
throughout the chapter — the cdf setting — which is why the Lean statement
carries `Monotone α`.)

## How `RSIntegrable` (Definition 1.2) is defined

`RSIntegrable` / the exported `def_1_2` predicate is **the upper/lower Darboux
common-limit criterion only** — exactly the textbook definition. In
[`def_1_2.lean`](def_1_2.lean):

```lean
/-- Upper and lower sums converge to a common limit `L` as the mesh → 0. -/
def UpperLowerCommonLimit (a b : ℝ) (f α : ℝ → ℝ) (L : ℝ) : Prop :=
  SourceHypotheses a b f α ∧
    ∀ eps > 0, ∃ delta > 0, ∀ P : Partition a b, P.mesh < delta →
      |upperSum P f α - L| < eps ∧ |lowerSum P f α - L| < eps

def RSIntegrableOnInterval (f α : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ L, UpperLowerCommonLimit a b f α L

/-- Exported statement of Definition 1.2. -/
def def_1_2 (f α : ℝ → ℝ) (a b : ℝ) : Prop :=
  DarbouxRS.RSIntegrableOnInterval f α a b
```

The book introduces the *tagged* Riemann–Stieltjes sum just before Definition
1.2, and its convergence follows **as a consequence** of the upper/lower
criterion — it is **not** part of the definition. That consequence is proved
separately as `taggedBridgeObligation`
(`UpperLowerCommonLimit → TaggedCommonLimit`) and exported as
`taggedCommonLimit_of_upperLowerCommonLimit`, so the public Definition 1.2
predicate is not made stronger than the textbook's.

## Scope and provisional integration rule

The 23 task files and 22 required support files in this directory form the
reviewed Chapter 1 bundle. The Riemann–Stieltjes and Dirichlet–Gamma support
files are included because reviewed examples/problems import them; unused
legacy aggregators and superseded proof shims are not included.

When Kenneth already has a file, his latest `main` version remains the source
for textbook wording and the public interface. The reviewed file here supplies
the proof to reconcile into that base before a PR is proposed. For example,
the reviewed `Ex_1_3_1.lean` here is a proof input for reconciling Kenneth's
newer file; it is not evidence that Kenneth's current file has already passed
review. This rule is provisional and may be revised after author feedback.
