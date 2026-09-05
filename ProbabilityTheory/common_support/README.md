# Shared support, bridge, and library modules

These modules provide reusable mathematics imported by more than one textbook
task, or stable interface machinery too general to belong to a single task.
All imports now use the `ProbabilityTheory.*` package layout.

| Location | Lean namespace | Role |
|---|---|---|
| `ProbabilityTheory/common_support/*.lean` | `ProbabilityTheory.common_support.*` | Shared chapter support and mathematical bridges |
| `ProbabilityTheory/Support/` | `ProbabilityTheory.Support.*` | Reusable iid-word library |
| `ProbabilityTheory/Phase2/` | `ProbabilityTheory.Phase2.*` | General measure-theory bridge lemmas |

## `ProbabilityTheory.common_support`

| File | Role |
|---|---|
| `rs_partition_core.lean` | Core tagged-partition and Riemann–Stieltjes definitions (`RSCore`) |
| `ch8_bernoulli_bool_core.lean` | Bernoulli law on `Bool` |
| `ch8_discrete_pmf_core.lean` | Poisson and Bernoulli PMFs on `ℕ` |
| `tv_distance_core.lean` | Total-variation distance for mass functions on `ℕ` |
| `chapter13_stopping_support.lean` | One-indexed stopped sums and natural filtrations |
| `chapter14_coupon_geometric_support.lean` | Coupon/waiting-time geometric formulas |
| `chapter14_mgf_support.lean` | Shared moment-generating-function interface |
| `chapter14_tightness_support.lean` | Tail-mass formulation of tightness |
| `chapter14_triangular_array_support.lean` | Triangular-array row and variance notation |
| `etemadi_pairwise_iid_slln.lean` | Etemadi strong law adapter for pairwise-iid sequences |
| `gamma_beta_bridge.lean` | Gamma/Beta/Dirichlet density definitions |
| `dirichlet_simplex_bridge.lean` | Ambient-nullity fact for the standard simplex |

## Other shared namespaces

| File | Module | Role |
|---|---|---|
| `ProbabilityTheory/Support/IIDWord.lean` | `ProbabilityTheory.Support.IIDWord` | Infinite iid finite-alphabet words and repeated-block result |
| `ProbabilityTheory/Phase2/DensityIntegralBridge.lean` | `ProbabilityTheory.Phase2.DensityIntegralBridge` | `withDensity`, set-integral, and integrability bridges |
| `ProbabilityTheory/Phase2/VectorMeasureBorelBridge.lean` | `ProbabilityTheory.Phase2.VectorMeasureBorelBridge` | Generator-extension bridge for vector measures |

Task-specific proof layers stay beside their parent in
`ProbabilityTheory/chapter_XX/`; they are indexed as
`task_owned_support_module` in the root manifest.
