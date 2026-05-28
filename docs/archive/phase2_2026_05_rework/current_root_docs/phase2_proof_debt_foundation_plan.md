# Phase 2 Proof-Debt Foundation Plan

This note records how to treat large accepted proof debt after the debt ledger
has been normalized. The immediate model is `thm_9_5`; the immediate target is
`thm_10_8`.

## What `thm_9_5` Did Correctly

`thm_9_5` did not try to prove the inversion formula in one public theorem
file. It split the textbook proof into reusable foundation layers:

- `thm_9_5_fubini.lean`: finite-cutoff integrability, product Fubini, and
  interval/product bridge.
- `thm_9_5_dirichlet.lean`: the Dirichlet integral and sine primitive facts.
- `thm_9_5_kernel.lean`: change of variables, pointwise kernel limits,
  measurability, and domination.
- `thm_9_5.lean`: final DCT and endpoint-mass assembly.

The important pattern is not just file splitting. `thm_9_5` first made the
source proof obligations auditable through a `SourceSpine`, then eliminated the
public scaffold by proving the fields internally:

```lean
theorem thm_9_5 (mu : Measure Real) [IsFiniteMeasure mu] :
    CharacteristicInversionFormula mu :=
  characteristicInversionFormula_of_sourceSpine mu
    <| CharacteristicInversionSourceSpine.mk
      characteristicInversionDirichletIntegralLimit_proof
```

The public theorem no longer asks downstream users to provide the source spine.
That is the standard for discharging proof debt.

## Current `thm_10_8` Shape

`thm_10_8` is still at the earlier `thm_9_5` stage:

- public theorem `thm_10_8` still requires `SkorokhodQuantileSupport`;
- three accepted debts remain fields of that support object;
- local Mathlib/ToyApollo search did not find an existing generalized inverse
  law-preservation or Skorokhod convergence API.

The debt is therefore not a missing few-line proof. It is a missing foundation
layer for quantile construction and law preservation.

## Recommended `thm_10_8` Foundation Split

Build the Skorokhod proof as separate files, following the `thm_9_5` model.

1. `thm_10_8_quantile_space.lean`
   - choose the common probability space;
   - use a real-line carrier with a unit-interval probability measure where
     possible, so it matches the current `SkorokhodRepresentation` witness
     shape;
   - prove the measure is a probability measure.

2. `thm_10_8_quantile_defs.lean`
   - define the CDF interface used by the construction;
   - define lower/upper generalized inverse functions;
   - connect the definitions to the textbook formulas.

3. `thm_10_8_quantile_law.lean`
   - prove measurability of the generalized inverse functions;
   - prove the CDF identity for the constructed variables;
   - prove law preservation by CDF equality.

4. `thm_10_8_quantile_convergence.lean`
   - prove the lower/upper inverse comparison from cdf convergence at
     continuity points;
   - use `prob_3_5` to control discontinuity points;
   - prove almost-sure convergence of the coupled variables.

5. `thm_10_8.lean`
   - keep `SkorokhodRepresentation` as the public conclusion;
   - keep a private/internal source-spine package only as assembly glue;
   - construct that spine from proved quantile lemmas;
   - remove `SkorokhodQuantileSupport` from the public theorem parameters.

## Reuse Targets

Once `thm_10_8` is discharged, the same work should reduce downstream debt in
`thm_14_2`:

- `thm_14_2_DistributionToWeakSupport.quantile_support` should disappear or
  become an internally constructed lemma;
- the remaining `thm_14_2` debt can then focus on continuous mapping,
  bounded dominated convergence, and the weak-to-cdf piecewise-linear
  approximation route.

## Similarity Scan Before New Wheels

Every large proof-debt repair should start with a similarity scan. The scan is
not optional: many apparent theorem-local gaps are actually the same missing
foundation under different names.

The scan does not change the proof spine. The source textbook proof remains the
primary decomposition, and Mathlib is mainly the formal substrate used to
implement those steps. A high-level Mathlib theorem can discharge a source step
only when the local Lean wrapper makes the correspondence explicit; otherwise
it is just another black-box bridge.

Check, in this order:

- the source proof span and its textbook-order obligations;
- `ToyApollo/Output` for older textbook task files, definition files, bridge
  files, and earlier local foundation files;
- proof-obligation ledgers for tasks with the same `kind`, theorem family, or
  bridge name;
- direct downstream users, because downstream tasks often reveal the intended
  reusable interface better than the current task does.
- Mathlib for atomic APIs or source-aligned theorem implementations.

If two tasks need the same bridge, build one shared foundation and let both
tasks import it. Do not keep separate theorem-local support structures unless
the source assumptions are genuinely different.

## Batch-One Shared Foundations

The current first bridge batch should be grouped by reusable foundations:

- `thm_10_8` and `thm_14_2` share Skorokhod/quantile and
  distribution-to-weak foundations.
- `thm_13_17` and `thm_13_18` share stopped-process measurability,
  integrability, and optional-stopping assembly foundations.
- `thm_14_4` should reuse total-variation/Radon-Nikodym density foundations
  already related to `thm_8_6`, `thm_13_5`, and the weak-convergence bridge.
- `thm_14_7` should reuse characteristic-function and triangular-array
  foundations from Chapter 9 and Chapter 14 rather than creating a CLT-specific
  black box.

## Next Practical Step

Do not keep re-running `debt-fix` expecting it to write the foundation. The next
engineering step is to create the first foundation file, probably
`thm_10_8_quantile_space.lean`, and make it build before touching the public
`thm_10_8` theorem.

The acceptance criterion for this first step is narrow:

- new file imports cleanly;
- it defines the unit-interval probability-space witness;
- it proves the witness has total mass one;
- it introduces no public support parameter or accepted proof debt.

Current first slice:

- `ToyApollo/Output/thm_10_8_quantile_space.lean` defines
  `thm_10_8_unitIntervalMeasure`.
- It proves `thm_10_8_unitIntervalMeasure_univ`.
- It registers `IsProbabilityMeasure thm_10_8_unitIntervalMeasure`.
- It proves the unit interval has full mass under that witness measure.

Current second slice:

- `ToyApollo/Output/thm_10_8_quantile_defs.lean` defines the reusable
  probability-CDF wrapper.
- It defines lower and upper generalized inverse quantiles, their defining
  sets, variables, and sequences.
- `ToyApollo/Output/thm_10_8.lean` imports these foundation files and no
  longer exposes `common_unit_interval_space` or
  `generalized_inverse_quantiles` as public proof-debt fields.
- `phase2_prompt_packs/thm_10_8/proof_obligations.json` now records those two
  obligations as proved; the remaining debts are law preservation,
  lower/upper inverse comparison, and almost-sure convergence.

Batch-one reuse result:

- `ToyApollo/Output/thm_14_7.lean` now proves
  `thm_14_7_triangularPowerLimit_proved` from Mathlib's complex exponential
  power-limit theorem.
- The CLT setup no longer asks downstream users to provide
  `triangular_power_limit`; only the concrete characteristic-function
  convergence data remains as support.

Stopped-value representative result:

- `ToyApollo/Output/thm_13_18.lean` now defines the canonical real-valued
  representative `thm_13_18_stoppedValueReal`.
- `thm_13_18_stoppedValueReal_agreement` proves that representative satisfies
  the finite stopped-value agreement interface, and
  `thm_13_18_stoppedValueReal_matches_option` connects it to Definition 13.8's
  Option-valued stopped value.
- `thm_13_18_canonical` exposes the source-aligned theorem using the canonical
  representative internally. The remaining `thm_13_18` proof debt is therefore
  only the two dominated-convergence routes in cases (ii) and (iii).
