/-
TASK ID: prob_2_6
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.def_2_4
import ToyApollo.Output.thm_2_1

theorem prob_2_6 (Ω : Type _) (A : ℕ → Set Ω) :
    (⋃ n : ℕ, ⋂ i ≥ n, A i) ⊆ (⋂ n : ℕ, ⋃ i ≥ n, A i) := by
      intro ω hω;
      simp +zetaDelta at *;
      exact fun n => ⟨ _, le_max_left _ _, hω.choose_spec _ ( le_max_right _ _ ) ⟩
