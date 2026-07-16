import Mathlib
import ToyApollo.Output.thm_4_7
import ToyApollo.Output.def_4_3_limsup_liminf

/-!
# Measurability of sequence limsup, liminf, and pointwise limits

Tail suprema and infima, then the outer liminf and limsup, are obtained by
repeatedly applying Theorem 4.7.  Filter bridges identify these textbook
formulas with the limits used by the pointwise convergence criterion.
-/

open MeasureTheory
open scoped Topology

/-!
Theorem 4.8: measurability of limsup and liminf of measurable `EReal`-valued
functions, plus a packaged criterion for measurability of a pointwise limit.
-/

theorem measurable_tailSupEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) (n : ℕ) :
    Measurable (fun ω => tailSup (fun i => f i ω) n) := by
  have htail : ∀ k, Measurable (fun ω => f (n + k) ω) := fun k => hf (n + k)
  simpa [tailSup, seqSup] using (thm_4_7 (fun k ω => f (n + k) ω) htail).1

theorem measurable_tailInfEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) (n : ℕ) :
    Measurable (fun ω => tailInf (fun i => f i ω) n) := by
  have htail : ∀ k, Measurable (fun ω => f (n + k) ω) := fun k => hf (n + k)
  simpa [tailInf, seqInf] using (thm_4_7 (fun k ω => f (n + k) ω) htail).2

theorem measurable_seqLimsupEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun ω => seqLimsup (fun i => f i ω)) := by
  have htails : ∀ n, Measurable (fun ω => tailSup (fun i => f i ω) n) :=
    fun n => measurable_tailSupEReal f hf n
  simpa [seqLimsup, seqInf] using
    (thm_4_7 (fun n ω => tailSup (fun i => f i ω) n) htails).2

theorem measurable_seqLiminfEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun ω => seqLiminf (fun i => f i ω)) := by
  have htails : ∀ n, Measurable (fun ω => tailInf (fun i => f i ω) n) :=
    fun n => measurable_tailInfEReal f hf n
  simpa [seqLiminf, seqSup] using
    (thm_4_7 (fun n ω => tailInf (fun i => f i ω) n) htails).1

theorem seqLimsup_eq_filter_limsupEReal (u : ℕ → EReal) :
    seqLimsup u = Filter.limsup u Filter.atTop := by
  simpa [seqLimsup, tailSup, Nat.add_comm] using
    (Filter.limsup_eq_iInf_iSup_of_nat' (u := u)).symm

theorem seqLiminf_eq_filter_liminfEReal (u : ℕ → EReal) :
    seqLiminf u = Filter.liminf u Filter.atTop := by
  simpa [seqLiminf, tailInf, Nat.add_comm] using
    (Filter.liminf_eq_iSup_iInf_of_nat' (u := u)).symm

theorem measurable_of_tendstoEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) {g : Ω → EReal}
    (hg : ∀ ω, Filter.Tendsto (fun n => f n ω) Filter.atTop (𝓝 (g ω))) :
    Measurable g := by
  have h_eq : g = fun ω => seqLimsup (fun i => f i ω) := by
    funext ω
    have h_limsup :
        Filter.limsup (fun n => f n ω) Filter.atTop ≤ g ω := by
      rw [Filter.limsup_le_iff]
      intro y hy
      exact (hg ω) (Iio_mem_nhds hy)
    have h_liminf :
        g ω ≤ Filter.liminf (fun n => f n ω) Filter.atTop := by
      rw [Filter.le_liminf_iff]
      intro y hy
      exact (hg ω) (Ioi_mem_nhds hy)
    have h_ge_limsup :
        g ω ≤ Filter.limsup (fun n => f n ω) Filter.atTop := by
      exact le_trans h_liminf (Filter.liminf_le_limsup (u := fun n => f n ω) (f := Filter.atTop))
    calc
      g ω = Filter.limsup (fun n => f n ω) Filter.atTop := le_antisymm h_ge_limsup h_limsup
      _ = seqLimsup (fun n => f n ω) := (seqLimsup_eq_filter_limsupEReal (fun n => f n ω)).symm
  rw [h_eq]
  exact measurable_seqLimsupEReal f hf

/-- Textbook theorem 4.8 in bundled form. -/
theorem thm_4_8 {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) {g : Ω → EReal}
    (hg : ∀ ω, Filter.Tendsto (fun n => f n ω) Filter.atTop (𝓝 (g ω))) :
    Measurable (fun ω => seqLimsup (fun i => f i ω)) ∧
      Measurable (fun ω => seqLiminf (fun i => f i ω)) ∧
      Measurable g := by
  exact ⟨measurable_seqLimsupEReal f hf, measurable_seqLiminfEReal f hf,
    measurable_of_tendstoEReal f hf hg⟩
