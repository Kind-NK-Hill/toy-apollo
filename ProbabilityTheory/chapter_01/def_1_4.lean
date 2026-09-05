/-
TASK ID: def_1_4
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_01.def_1_2




open Filter

noncomputable section



def improperRSFilter : Filter (ℝ × ℝ) :=
  (atBot ×ˢ atTop) ⊓ Filter.principal {p : ℝ × ℝ | p.1 ≤ p.2}

 
noncomputable def rsTruncIntegral (f α : ℝ → ℝ) (a b : ℝ) : ℝ :=
  by
    classical
    exact if h : RSIntegrable f α a b then rsIntegral f α a b h else 0

 
def ImproperRSConvergesTo (f α : ℝ → ℝ) (I : ℝ) : Prop :=
  (∀ᶠ p : ℝ × ℝ in improperRSFilter, RSIntegrable f α p.1 p.2) ∧
    Tendsto
      (fun p : ℝ × ℝ => rsTruncIntegral f α p.1 p.2)
      improperRSFilter
      (nhds I)

 
def ImproperRSIntegrable (f α : ℝ → ℝ) : Prop :=
  ∃ I : ℝ, ImproperRSConvergesTo f α I



noncomputable def improperRSIntegral
  (f α : ℝ → ℝ) (h : ImproperRSIntegrable f α) : ℝ :=
  Classical.choose h

 
theorem improperRSIntegral_spec {f α : ℝ → ℝ} (h : ImproperRSIntegrable f α) :
    ImproperRSConvergesTo f α (improperRSIntegral f α h) :=
  Classical.choose_spec h



def def_1_4 (f α : ℝ → ℝ) : Prop :=
  ImproperRSIntegrable f α
