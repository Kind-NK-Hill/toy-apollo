import ToyApollo.Output.prob_7_3_completion_support

/-!
Parent-owned support facade for Problem 7.3.

The proof body is split into:

- prob_7_3_oscillation_support: large-oscillation layers, measurability, and basic RS/LS bridges;
- prob_7_3_partition_support: atom-free partitions and protected endpoint construction;
- prob_7_3_forward_support: protected cell covers and the RS-integrable-to-a.e.-continuity route;
- prob_7_3_completion_support: the reverse Darboux estimate, part (a), completion transfer, and final support result.

This facade keeps the parent import stable while preventing a single 3000-line
task-owned proof container.
-/
