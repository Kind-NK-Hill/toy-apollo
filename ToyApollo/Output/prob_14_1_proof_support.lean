import ToyApollo.Output.prob_14_1_tail_support

/-!
Parent-owned support facade for Problem 14.1.

The proof body is split into:

- `prob_14_1_asymptotic_support`: rising-factorial, Gamma/Beta, and local asymptotics;
- `prob_14_1_finite_law_support`: finite Polya path/count laws;
- `prob_14_1_grid_cdf_support`: scaled grid CDF and CDF-to-weak interface;
- `prob_14_1_tail_support`: endpoint tails and final convergence assembly.

This facade keeps the parent import stable while preventing the task-facing
support file from owning a 5000-line proof body.
-/
