import ToyApollo.Output.prob_8_6_final_support

/-!
Parent-owned support facade for Problem 8.6.

The proof body is split into:

- prob_8_6_basic_support: real PMF definitions, convolution definitions, and basic TV facts;
- prob_8_6_single_step_support: Bernoulli-Poisson one-step coupling and mismatch bounds;
- prob_8_6_convolution_support: TV contraction under convolution and n-fold bounds;
- prob_8_6_component_support: non-identically distributed component sums and part (c);
- prob_8_6_final_support: arithmetic specialization, part (d), and prob_8_6_support_result.

This facade keeps the parent import stable while moving the proof route out of
the task-facing theorem file.
-/
