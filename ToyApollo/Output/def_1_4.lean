/-
TASK ID: def_1_4
TYPE: Definition
SOURCE PLAN: 38_chap1_riemann_stieltjes
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_1_2

-- WRITE FINAL LEAN CODE BELOW

open Filter

noncomputable section

def improperRSFilter : Filter (ℝ × ℝ) :=
  (atBot ×ˢ atTop) ⊓ Filter.principal {p : ℝ × ℝ | p.1 ≤ p.2}

noncomputable def rsTruncIntegral (f α : ℝ → ℝ) (a b : ℝ)
    (h : RSIntegrable f α a b) : ℝ :=
  rsIntegral f α a b h

@[simp] theorem rsTruncIntegral_eq_rsIntegral {f α : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f α a b) :
    rsTruncIntegral f α a b h = rsIntegral f α a b h :=
  rfl

theorem rsTruncIntegral_proof_irrel {f α : ℝ → ℝ} {a b : ℝ}
    (h₁ h₂ : RSIntegrable f α a b) :
    rsTruncIntegral f α a b h₁ = rsTruncIntegral f α a b h₂ := by
  congr

def ImproperRSConvergesTo (f α : ℝ → ℝ) (I : ℝ) : Prop :=
  ∀ ε > 0,
    ∀ᶠ p : ℝ × ℝ in improperRSFilter,
      ∃ h : RSIntegrable f α p.1 p.2,
        dist (rsTruncIntegral f α p.1 p.2 h) I < ε

theorem ImproperRSConvergesTo.of_tendsto {f α : ℝ → ℝ} {I : ℝ}
    {u : ℝ × ℝ → ℝ}
    (hrep :
      ∀ᶠ p : ℝ × ℝ in improperRSFilter,
        ∃ h : RSIntegrable f α p.1 p.2,
          u p = rsTruncIntegral f α p.1 p.2 h)
    (hlim : Tendsto u improperRSFilter (nhds I)) :
    ImproperRSConvergesTo f α I := by
  intro ε hε
  have hclose : ∀ᶠ p : ℝ × ℝ in improperRSFilter, dist (u p) I < ε :=
    (Metric.tendsto_nhds.mp hlim) ε hε
  filter_upwards [hrep, hclose] with p hp hdist
  rcases hp with ⟨h, hu⟩
  exact ⟨h, by simpa [hu] using hdist⟩

theorem ImproperRSConvergesTo.eventually_rsIntegrable {f α : ℝ → ℝ} {I : ℝ}
    (h : ImproperRSConvergesTo f α I) :
    ∀ᶠ p : ℝ × ℝ in improperRSFilter, RSIntegrable f α p.1 p.2 := by
  filter_upwards [h 1 zero_lt_one] with p hp
  exact hp.choose

theorem improperRSFilter_neBot : NeBot improperRSFilter := by
  unfold improperRSFilter
  rw [Filter.inf_neBot_iff]
  intro s hs t ht
  rw [Filter.mem_prod_iff] at hs
  rcases hs with ⟨A, hA, B, hB, hsub⟩
  rcases (Filter.eventually_atBot.mp hA) with ⟨a₀, hA₀⟩
  rcases (Filter.eventually_atTop.mp hB) with ⟨b₀, hB₀⟩
  let x : ℝ := min a₀ b₀
  let y : ℝ := max b₀ x
  have hxA : x ∈ A := hA₀ x (min_le_left a₀ b₀)
  have hyB : y ∈ B := hB₀ y (le_max_left b₀ x)
  have hxy : x ≤ y := le_max_right b₀ x
  have ht_sub : {p : ℝ × ℝ | p.1 ≤ p.2} ⊆ t := by
    simpa using ht
  exact ⟨(x, y), hsub ⟨hxA, hyB⟩, ht_sub hxy⟩

theorem ImproperRSConvergesTo.unique {f α : ℝ → ℝ} {I J : ℝ}
    (hI : ImproperRSConvergesTo f α I)
    (hJ : ImproperRSConvergesTo f α J) :
    I = J := by
  by_contra hne
  have hd : 0 < dist I J := dist_pos.mpr hne
  let ε : ℝ := dist I J / 3
  have hε : 0 < ε := div_pos hd (by norm_num)
  have hboth : ∀ᶠ p : ℝ × ℝ in improperRSFilter, False := by
    filter_upwards [hI ε hε, hJ ε hε] with p hpI hpJ
    rcases hpI with ⟨hi, hi_close⟩
    rcases hpJ with ⟨hj, hj_close⟩
    have hvalues :
        rsTruncIntegral f α p.1 p.2 hi =
          rsTruncIntegral f α p.1 p.2 hj :=
      rsTruncIntegral_proof_irrel hi hj
    have htriangle :
        dist I J ≤
          dist I (rsTruncIntegral f α p.1 p.2 hi) +
            dist (rsTruncIntegral f α p.1 p.2 hi) J :=
      dist_triangle _ _ _
    have hlt : dist I J < ε + ε := by
      refine lt_of_le_of_lt htriangle (add_lt_add ?_ ?_)
      · simpa [dist_comm] using hi_close
      · simpa [hvalues] using hj_close
    dsimp [ε] at hlt
    have hd_nonneg : 0 ≤ dist I J := dist_nonneg
    nlinarith
  letI : NeBot improperRSFilter := improperRSFilter_neBot
  rcases hboth.exists with ⟨_, hfalse⟩
  exact hfalse

def ImproperRSIntegrable (f α : ℝ → ℝ) : Prop :=
  ∃ I : ℝ, ImproperRSConvergesTo f α I

noncomputable def improperRSIntegral (f α : ℝ → ℝ) (h : ImproperRSIntegrable f α) : ℝ :=
  Classical.choose h

theorem improperRSIntegral_spec {f α : ℝ → ℝ} (h : ImproperRSIntegrable f α) :
    ImproperRSConvergesTo f α (improperRSIntegral f α h) :=
  Classical.choose_spec h

theorem improperRSIntegral_eq_of_convergesTo {f α : ℝ → ℝ} {I : ℝ}
    (h : ImproperRSConvergesTo f α I) :
    improperRSIntegral f α ⟨I, h⟩ = I :=
  (improperRSIntegral_spec ⟨I, h⟩).unique h

def def_1_4 (f α : ℝ → ℝ) : Prop :=
  ImproperRSIntegrable f α
