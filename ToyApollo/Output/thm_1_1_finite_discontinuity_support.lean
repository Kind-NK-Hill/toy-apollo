import ToyApollo.Output.thm_1_1_common_limit

open Finset BigOperators
open MeasureTheory Set Topology

/-!
Proof-spine aggregation module for Theorem 1.1.

This module re-exports the finite-discontinuity Darboux proof spine
(`Thm11SourceRoute.strict_thm_1_1` and its supporting lemmas), assembled from:

- `ToyApollo.Output.thm_1_1_basic`
- `ToyApollo.Output.thm_1_1_oscillation`
- `ToyApollo.Output.thm_1_1_refinement`
- `ToyApollo.Output.thm_1_1_finite_discontinuity`
- `ToyApollo.Output.thm_1_1_common_limit`

The final theorem statement `thm_1_1` now lives in `ToyApollo.Output.thm_1_1`,
which imports this module. Keeping this module as the spine seam preserves the
existing import graph while making Theorem 1.1 itself the readable entry point.
-/
