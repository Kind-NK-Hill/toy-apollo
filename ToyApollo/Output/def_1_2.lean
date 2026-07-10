/-
TASK ID: def_1_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open Finset BigOperators

open Set
open scoped Pointwise
open scoped Classical

noncomputable section

namespace DarbouxRS

def SourceHypotheses (a b : ℝ) (f alpha : ℝ → ℝ) : Prop :=
  a < b ∧
  BddAbove (f '' Set.Icc a b) ∧
  BddBelow (f '' Set.Icc a b) ∧
  MonotoneOn alpha (Set.Icc a b)

structure Partition (a b : ℝ) where
  n : ℕ
  hn : 0 < n
  pts : Fin (n + 1) → ℝ
  pts_start : pts 0 = a
  pts_end : pts (Fin.last n) = b
  strict_mono : StrictMono pts

def Partition.mesh {a b : ℝ} (P : Partition a b) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin P.n))
    ⟨⟨0, P.hn⟩, Finset.mem_univ _⟩
    fun i => P.pts i.succ - P.pts i.castSucc

def Partition.subinterval {a b : ℝ} (P : Partition a b) (i : Fin P.n)
  : Set ℝ :=
  Set.Icc (P.pts i.castSucc) (P.pts i.succ)

abbrev subinterval {a b : ℝ} (P : Partition a b) (i : Fin P.n) : Set ℝ :=
  P.subinterval i

def upperStep {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) (i : Fin P.n) : ℝ :=
  sSup (f '' Partition.subinterval P i)

def lowerStep {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) (i : Fin P.n) : ℝ :=
  sInf (f '' Partition.subinterval P i)

open scoped BigOperators

def taggedSum {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    f (tags i) * (alpha (P.pts i.succ) - alpha (P.pts i.castSucc))

def tagsInPartition {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ) : Prop :=
  ∀ i : Fin P.n, tags i ∈ Partition.subinterval P i

example {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ) :
  tagsInPartition P tags ↔ ∀ i : Fin P.n, tags i ∈ Set.Icc (P.pts i.castSucc) (P.pts i.succ)
  := by rfl

def upperSum {a b : ℝ} (P : Partition a b) (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    upperStep P f i * (alpha (P.pts i.succ) - alpha (P.pts i.castSucc))

def lowerSum {a b : ℝ} (P : Partition a b) (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    lowerStep P f i * (alpha (P.pts i.succ) - alpha (P.pts i.castSucc))

def UpperLowerCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  SourceHypotheses a b f alpha ∧
    ∀ eps > 0, ∃ delta > 0, ∀ P : Partition a b,
      P.mesh < delta →
        |upperSum P f alpha - L| < eps ∧ |lowerSum P f alpha - L| < eps

def RSIntegrableOnInterval (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ L, UpperLowerCommonLimit a b f alpha L

def TaggedCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  SourceHypotheses a b f alpha ∧
    ∀ eps > 0, ∃ delta > 0, ∀ P : Partition a b, ∀ tags : Fin P.n → ℝ,
      tagsInPartition P tags →
      P.mesh < delta →
      |taggedSum P tags f alpha - L| < eps

end DarbouxRS

abbrev RSPartition := DarbouxRS.Partition

def rsPartitionMesh {a b : ℝ} (P : RSPartition a b) : ℝ :=
  DarbouxRS.Partition.mesh P

def rsUpperSum {a b : ℝ} (P : RSPartition a b) (f alpha : ℝ → ℝ) : ℝ :=
  DarbouxRS.upperSum P f alpha

def rsLowerSum {a b : ℝ} (P : RSPartition a b) (f alpha : ℝ → ℝ) : ℝ :=
  DarbouxRS.lowerSum P f alpha

def rsUpperLowerCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  DarbouxRS.UpperLowerCommonLimit a b f alpha L

def rsTaggedCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  DarbouxRS.TaggedCommonLimit a b f alpha L

structure RSIntegralWitness (f alpha : ℝ → ℝ) (a b : ℝ) where
  value : ℝ
  source_limit : rsUpperLowerCommonLimit a b f alpha value

def RSIntegrable (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  DarbouxRS.RSIntegrableOnInterval f alpha a b

def RSIntegralWitness.toRSIntegrable {f alpha : ℝ → ℝ} {a b : ℝ}
    (w : RSIntegralWitness f alpha a b) : RSIntegrable f alpha a b :=
  ⟨w.value, w.source_limit⟩

noncomputable def rsIntegral (f alpha : ℝ → ℝ) (a b : ℝ)
    (h : RSIntegrable f alpha a b) : ℝ :=
  Classical.choose h

theorem rsIntegral_source_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsUpperLowerCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  Classical.choose_spec h

def def_1_2 (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  RSIntegrable f alpha a b

def rsIntegrableFamily (alpha : ℝ → ℝ) (a b : ℝ) : Set (ℝ → ℝ) :=
  {f | RSIntegrable f alpha a b}

namespace DarbouxRS

theorem sourceHypotheses_integrator_add {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    (h₁ : SourceHypotheses a b f α₁)
    (h₂ : SourceHypotheses a b f α₂) :
    SourceHypotheses a b f (fun x => α₁ x + α₂ x) := by
  rcases h₁ with ⟨hab, hAbove, hBelow, hmono₁⟩
  rcases h₂ with ⟨_hab₂, _hAbove₂, _hBelow₂, hmono₂⟩
  refine ⟨hab, hAbove, hBelow, ?_⟩
  intro x hx y hy hxy
  exact add_le_add (hmono₁ hx hy hxy) (hmono₂ hx hy hxy)

theorem upperSum_integrator_add {a b : ℝ} (P : Partition a b)
    (f α₁ α₂ : ℝ → ℝ) :
    upperSum P f (fun x => α₁ x + α₂ x) =
      upperSum P f α₁ + upperSum P f α₂ := by
  unfold upperSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem lowerSum_integrator_add {a b : ℝ} (P : Partition a b)
    (f α₁ α₂ : ℝ → ℝ) :
    lowerSum P f (fun x => α₁ x + α₂ x) =
      lowerSum P f α₁ + lowerSum P f α₂ := by
  unfold lowerSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem taggedSum_integrator_add {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (f α₁ α₂ : ℝ → ℝ) :
    taggedSum P tags f (fun x => α₁ x + α₂ x) =
      taggedSum P tags f α₁ + taggedSum P tags f α₂ := by
  unfold taggedSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

def uniformPartition (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 0 < n) :
    Partition a b where
  n := n
  hn := hn
  pts := fun i => a + ((i : ℝ) / (n : ℝ)) * (b - a)
  pts_start := by simp
  pts_end := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    -- Explicitly change the Fin coercion to expose its integer value
    change a + ((Fin.last n).val : ℝ) / (n : ℝ) * (b - a) = b
    rw [Fin.val_last]
    field_simp [hn0]
    ring
  strict_mono := by
    -- StrictMono means ∀ i j, i < j → pts i < pts j
    intro i j hij
    dsimp
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hba : 0 < b - a := sub_pos.mpr hab
    have hijR : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij

    -- Step 1: i < j  ==>  i / n < j / n
    have h1 : (i : ℝ) / (n : ℝ) < (j : ℝ) / (n : ℝ) := by
      exact mul_lt_mul_of_pos_right hijR (inv_pos.mpr hnR)

    -- Step 2: i / n * (b - a) < j / n * (b - a)
    have h2 : ((i : ℝ) / (n : ℝ)) * (b - a) < ((j : ℝ) / (n : ℝ)) * (b - a) :=
      mul_lt_mul_of_pos_right h1 hba

    -- Step 3: a + ... < a + ...
    linarith [h2]

theorem uniformPartition_mesh_eq (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 0 < n) :
    (uniformPartition a b hab n hn).mesh = (b - a) / (n : ℝ) := by
  unfold Partition.mesh uniformPartition
  apply Finset.sup'_eq_of_forall
  intro i hi
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp [ne_of_gt hnR]
  ring

theorem exists_partition_mesh_lt {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) :
    ∃ P : Partition a b, P.mesh < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  let N := n + 1
  have hNpos : 0 < N := Nat.succ_pos n
  refine ⟨uniformPartition a b hab N hNpos, ?_⟩
  rw [uniformPartition_mesh_eq]
  have hNposR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hltN : (b - a) / δ < (N : ℝ) := by
    have hnle : (n : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_succ_self n
    exact lt_trans hn hnle
  have hmul : b - a < (N : ℝ) * δ := by
    rwa [div_lt_iff₀ hδ] at hltN
  rw [div_lt_iff₀ hNposR]
  nlinarith

theorem leftTagsInPartition {a b : ℝ} (P : Partition a b) :
    tagsInPartition P (fun i => P.pts i.castSucc) := by
  intro i
  constructor
  · exact le_rfl
  · simp only
    apply le_of_lt
    exact P.strict_mono (Fin.castSucc_lt_succ)

lemma partition_pts_monotone_core {a b : ℝ} (P : Partition a b)
    {i j : Fin (P.n + 1)} (hij : i ≤ j) :
  P.pts i ≤ P.pts j := by
  exact P.strict_mono.monotone hij

lemma partition_pts_mem_Icc_core {a b : ℝ} (P : Partition a b) {i : Fin (P.n + 1)} :
    P.pts i ∈ Set.Icc a b := by
  constructor
  · calc
      a = P.pts 0 := P.pts_start.symm
      _ ≤ P.pts i := partition_pts_monotone_core P (Fin.zero_le i)
  · calc
      P.pts i ≤ P.pts (Fin.last P.n) := partition_pts_monotone_core P (Fin.le_last i)
      _ = b := P.pts_end

lemma subinterval_subset_Icc_core {a b : ℝ} (P : Partition a b) {i : Fin P.n} :
    Partition.subinterval P i ⊆ Set.Icc a b := by
  intro x hx
  constructor
  · -- a ≤ P.pts i.castSucc ≤ x
    exact le_trans (partition_pts_mem_Icc_core P).1 hx.1
  · -- x ≤ P.pts i.succ ≤ b
    exact le_trans hx.2 (partition_pts_mem_Icc_core P).2

theorem taggedCommonLimit_unique {a b : ℝ} {f alpha : ℝ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : TaggedCommonLimit a b f alpha L₁)
    (h₂ : TaggedCommonLimit a b f alpha L₂) :
    L₁ = L₂ := by
  rcases h₁ with ⟨hs₁, hlim₁⟩
  rcases h₂ with ⟨_hs₂, hlim₂⟩
  rcases hs₁ with ⟨hab, _⟩
  refine eq_of_forall_dist_le ?_
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlim₁ (eps / 2) hhalf with ⟨δ₁, hδ₁, H₁⟩
  rcases hlim₂ (eps / 2) hhalf with ⟨δ₂, hδ₂, H₂⟩
  rcases exists_partition_mesh_lt hab (lt_min hδ₁ hδ₂) with ⟨P, hPmesh⟩

  -- Define `tags` to precisely match the size `Fin P.n`
  let tags : Fin P.n → ℝ := fun i => P.pts i.castSucc

  -- `leftTagsInPartition P` provides exactly this proof.
  have htags : tagsInPartition P tags := leftTagsInPartition P

  have hmesh₁ : P.mesh < δ₁ := lt_of_lt_of_le hPmesh (min_le_left δ₁ δ₂)
  have hmesh₂ : P.mesh < δ₂ := lt_of_lt_of_le hPmesh (min_le_right δ₁ δ₂)

  have hP₁ := H₁ P tags htags hmesh₁
  have hP₂ := H₂ P tags htags hmesh₂
  have hdecomp :
      L₁ - L₂ = -(taggedSum P tags f alpha - L₁) +
        (taggedSum P tags f alpha - L₂) := by
    ring
  have hlt : |L₁ - L₂| < eps := by
    calc
      |L₁ - L₂| =
          |-(taggedSum P tags f alpha - L₁) +
            (taggedSum P tags f alpha - L₂)| := by rw [hdecomp]
      _ ≤ |-(taggedSum P tags f alpha - L₁)| +
            |taggedSum P tags f alpha - L₂| := abs_add_le _ _
      _ = |taggedSum P tags f alpha - L₁| +
            |taggedSum P tags f alpha - L₂| := by rw [abs_neg]
      _ < eps := by
        have hsum :
            |taggedSum P tags f alpha - L₁| +
                |taggedSum P tags f alpha - L₂| < eps / 2 + eps / 2 :=
          add_lt_add hP₁ hP₂
        simpa using hsum
  have hdist : dist L₁ L₂ < eps := by
    simpa [Real.dist_eq, abs_sub_comm] using hlt
  exact le_of_lt hdist

theorem upperLowerCommonLimit_integrator_add {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    {L₁ L₂ : ℝ}
    (h₁ : UpperLowerCommonLimit a b f α₁ L₁)
    (h₂ : UpperLowerCommonLimit a b f α₂ L₂) :
    UpperLowerCommonLimit a b f (fun x => α₁ x + α₂ x) (L₁ + L₂) := by
  rcases h₁ with ⟨hs₁, hlim₁⟩
  rcases h₂ with ⟨hs₂, hlim₂⟩
  refine ⟨sourceHypotheses_integrator_add hs₁ hs₂, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlim₁ (eps / 2) hhalf with ⟨δ₁, hδ₁, H₁⟩
  rcases hlim₂ (eps / 2) hhalf with ⟨δ₂, hδ₂, H₂⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro P hmesh
  have hmesh₁ : P.mesh < δ₁ := lt_of_lt_of_le hmesh (min_le_left δ₁ δ₂)
  have hmesh₂ : P.mesh < δ₂ := lt_of_lt_of_le hmesh (min_le_right δ₁ δ₂)
  have hP₁ := H₁ P hmesh₁
  have hP₂ := H₂ P hmesh₂
  constructor
  · have hadd :
        upperSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂) =
          (upperSum P f α₁ - L₁) + (upperSum P f α₂ - L₂) := by
      rw [upperSum_integrator_add]
      ring
    calc
      |upperSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂)| =
          |(upperSum P f α₁ - L₁) + (upperSum P f α₂ - L₂)| := by rw [hadd]
      _ ≤ |upperSum P f α₁ - L₁| + |upperSum P f α₂ - L₂| := abs_add_le _ _
      _ < eps := by
        have hlt :
            |upperSum P f α₁ - L₁| + |upperSum P f α₂ - L₂| <
              eps / 2 + eps / 2 := add_lt_add hP₁.1 hP₂.1
        simpa using hlt
  · have hadd :
        lowerSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂) =
          (lowerSum P f α₁ - L₁) + (lowerSum P f α₂ - L₂) := by
      rw [lowerSum_integrator_add]
      ring
    calc
      |lowerSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂)| =
          |(lowerSum P f α₁ - L₁) + (lowerSum P f α₂ - L₂)| := by rw [hadd]
      _ ≤ |lowerSum P f α₁ - L₁| + |lowerSum P f α₂ - L₂| := abs_add_le _ _
      _ < eps := by
        have hlt :
            |lowerSum P f α₁ - L₁| + |lowerSum P f α₂ - L₂| <
              eps / 2 + eps / 2 := add_lt_add hP₁.2 hP₂.2
        simpa using hlt

theorem taggedCommonLimit_integrator_add {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    {L₁ L₂ : ℝ}
    (h₁ : TaggedCommonLimit a b f α₁ L₁)
    (h₂ : TaggedCommonLimit a b f α₂ L₂) :
    TaggedCommonLimit a b f (fun x => α₁ x + α₂ x) (L₁ + L₂) := by
  rcases h₁ with ⟨hs₁, hlim₁⟩
  rcases h₂ with ⟨hs₂, hlim₂⟩
  refine ⟨sourceHypotheses_integrator_add hs₁ hs₂, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlim₁ (eps / 2) hhalf with ⟨δ₁, hδ₁, H₁⟩
  rcases hlim₂ (eps / 2) hhalf with ⟨δ₂, hδ₂, H₂⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro P tags htags hmesh
  have hmesh₁ : P.mesh < δ₁ := lt_of_lt_of_le hmesh (min_le_left δ₁ δ₂)
  have hmesh₂ : P.mesh < δ₂ := lt_of_lt_of_le hmesh (min_le_right δ₁ δ₂)
  have hP₁ := H₁ P tags htags hmesh₁
  have hP₂ := H₂ P tags htags hmesh₂
  have hadd :
      taggedSum P tags f (fun x => α₁ x + α₂ x) - (L₁ + L₂) =
        (taggedSum P tags f α₁ - L₁) + (taggedSum P tags f α₂ - L₂) := by
    rw [taggedSum_integrator_add]
    ring
  calc
    |taggedSum P tags f (fun x => α₁ x + α₂ x) - (L₁ + L₂)| =
        |(taggedSum P tags f α₁ - L₁) + (taggedSum P tags f α₂ - L₂)| := by
      rw [hadd]
    _ ≤ |taggedSum P tags f α₁ - L₁| + |taggedSum P tags f α₂ - L₂| :=
      abs_add_le _ _
    _ < eps := by
      have hlt :
          |taggedSum P tags f α₁ - L₁| + |taggedSum P tags f α₂ - L₂| <
            eps / 2 + eps / 2 := add_lt_add hP₁ hP₂
      simpa using hlt

theorem taggedSum_integrand_add {a b : ℝ}
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (f g alpha : ℝ → ℝ) :
  taggedSum P tags (fun x => f x + g x) alpha =
      taggedSum P tags f alpha + taggedSum P tags g alpha := by
  unfold taggedSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem sourceHypotheses_integrand_add {a b : ℝ} {f g alpha : ℝ → ℝ}
    (hf : SourceHypotheses a b f alpha)
    (hg : SourceHypotheses a b g alpha) :
    SourceHypotheses a b (fun x => f x + g x) alpha := by
  rcases hf with ⟨hab, hfAbove, hfBelow, hmono⟩
  rcases hg with ⟨_habg, hgAbove, hgBelow, _hmonog⟩
  refine ⟨hab, ?_, ?_, hmono⟩
  · refine BddAbove.mono ?_ (hfAbove.add hgAbove)
    rintro y ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, g x, ⟨x, hx, rfl⟩, rfl⟩
  · refine BddBelow.mono ?_ (hfBelow.add hgBelow)
    rintro y ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, g x, ⟨x, hx, rfl⟩, rfl⟩

theorem taggedCommonLimit_integrand_add {a b : ℝ} {f g alpha : ℝ → ℝ}
    {Lf Lg : ℝ}
    (hf : TaggedCommonLimit a b f alpha Lf)
    (hg : TaggedCommonLimit a b g alpha Lg) :
    TaggedCommonLimit a b (fun x => f x + g x) alpha (Lf + Lg) := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨hsg, hlimg⟩
  refine ⟨sourceHypotheses_integrand_add hsf hsg, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro P tags htags hmesh
  have hmeshf : P.mesh < δf := lt_of_lt_of_le hmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hmesh (min_le_right δf δg)
  have hPf := Hf P tags htags hmeshf
  have hPg := Hg P tags htags hmeshg
  have hadd :
      taggedSum P tags (fun x => f x + g x) alpha - (Lf + Lg) =
        (taggedSum P tags f alpha - Lf) +
          (taggedSum P tags g alpha - Lg) := by
    rw [taggedSum_integrand_add]
    ring
  calc
    |taggedSum P tags (fun x => f x + g x) alpha - (Lf + Lg)| =
        |(taggedSum P tags f alpha - Lf) +
          (taggedSum P tags g alpha - Lg)| := by
      rw [hadd]
    _ ≤ |taggedSum P tags f alpha - Lf| +
        |taggedSum P tags g alpha - Lg| := abs_add_le _ _
    _ < eps := by
      have hlt :
          |taggedSum P tags f alpha - Lf| +
            |taggedSum P tags g alpha - Lg| < eps / 2 + eps / 2 :=
        add_lt_add hPf hPg
      simpa using hlt

lemma upperStep_integrand_add_le_core {a b : ℝ}
    {f g : ℝ → ℝ}
    (P : Partition a b)
    (i : Fin P.n)
    (hfAbove : BddAbove (f '' Set.Icc a b))
    (hgAbove : BddAbove (g '' Set.Icc a b)) :
    upperStep P (fun x => f x + g x) i ≤ upperStep P f i + upperStep P g i := by
  have hcell_nonempty : ((fun x => f x + g x) '' Partition.subinterval P i).Nonempty := by
    -- Evaluate the function at the left endpoint of the interval
    refine ⟨f (P.pts i.castSucc) + g (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc, ⟨le_rfl, le_of_lt (P.strict_mono (Fin.castSucc_lt_succ))⟩, rfl⟩

  have hfCellAbove : BddAbove (f '' Partition.subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hfAbove

  have hgCellAbove : BddAbove (g '' Partition.subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hgAbove

  unfold upperStep
  refine csSup_le hcell_nonempty ?_
  rintro y ⟨x, hx, rfl⟩

  have hfx : f x ≤ sSup (f '' Partition.subinterval P i) :=
    le_csSup hfCellAbove ⟨x, hx, rfl⟩

  have hgx : g x ≤ sSup (g '' Partition.subinterval P i) :=
    le_csSup hgCellAbove ⟨x, hx, rfl⟩

  linarith

lemma lowerStep_integrand_add_le_core {a b : ℝ} {f g : ℝ → ℝ}
    (P : Partition a b)
    (i : Fin P.n)
    (hfBelow : BddBelow (f '' Set.Icc a b))
    (hgBelow : BddBelow (g '' Set.Icc a b)) :
    lowerStep P f i + lowerStep P g i ≤ lowerStep P (fun x => f x + g x) i := by
  have hcell_nonempty : ((fun x => f x + g x) '' Partition.subinterval P i).Nonempty := by
    -- Evaluate the function at the left endpoint of the interval
    refine ⟨f (P.pts i.castSucc) + g (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc, ⟨le_rfl, le_of_lt (P.strict_mono (Fin.castSucc_lt_succ))⟩, rfl⟩

  have hfCellBelow : BddBelow (f '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hfBelow

  have hgCellBelow : BddBelow (g '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hgBelow

  unfold lowerStep
  refine le_csInf hcell_nonempty ?_
  rintro y ⟨x, hx, rfl⟩

  have hfx : sInf (f '' Partition.subinterval P i) ≤ f x :=
    csInf_le hfCellBelow ⟨x, hx, rfl⟩

  have hgx : sInf (g '' Partition.subinterval P i) ≤ g x :=
    csInf_le hgCellBelow ⟨x, hx, rfl⟩

  linarith

lemma image_const_mul_Icc_eq_smul_core {a b c : ℝ} (f : ℝ → ℝ) :
    (fun x => c * f x) '' Icc a b = c • (f '' Icc a b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [smul_eq_mul]⟩

theorem sourceHypotheses_const_mul_core {a b c : ℝ} {f alpha : ℝ → ℝ}
    (h : SourceHypotheses a b f alpha) :
    SourceHypotheses a b (fun x => c * f x) alpha := by
  rcases h with ⟨hab, hAbove, hBelow, hmono⟩
  refine ⟨hab, ?_, ?_, hmono⟩
  · by_cases hc : 0 ≤ c
    · rw [image_const_mul_Icc_eq_smul_core]
      exact hAbove.smul_of_nonneg hc
    · have hc' : c ≤ 0 := le_of_not_ge hc
      rw [image_const_mul_Icc_eq_smul_core]
      exact BddBelow.smul_of_nonpos hc' hBelow
  · by_cases hc : 0 ≤ c
    · rw [image_const_mul_Icc_eq_smul_core]
      exact hBelow.smul_of_nonneg hc
    · have hc' : c ≤ 0 := le_of_not_ge hc
      rw [image_const_mul_Icc_eq_smul_core]
      exact BddAbove.smul_of_nonpos hc' hAbove

lemma partition_increment_nonneg_of_source_core {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) {i : Fin P.n} :
    0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) := by
  -- Unpack the SourceHypotheses to get the monotonicity of alpha
  rcases hs with ⟨_hab, _hAbove, _hBelow, hmono⟩

  -- The endpoints of the subinterval are in [a, b]
  have hleft : P.pts i.castSucc ∈ Set.Icc a b := partition_pts_mem_Icc_core P
  have hright : P.pts i.succ ∈ Set.Icc a b := partition_pts_mem_Icc_core P

  -- Because x_i < x_{i+1}, monotonicity implies alpha(x_i) ≤ alpha(x_{i+1})
  have h_pts_lt : P.pts i.castSucc < P.pts i.succ :=
    P.strict_mono (Fin.castSucc_lt_succ)

  exact sub_nonneg.mpr (hmono hleft hright (le_of_lt h_pts_lt))

theorem upperSum_integrand_add_le_core {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    upperSum P (fun x => f x + g x) alpha ≤
      upperSum P f alpha + upperSum P g alpha := by
  rcases hsf with ⟨_hab, hfAbove, _hfBelow, _hmono⟩
  rcases hsg with ⟨_habg, hgAbove, _hgBelow, _hmonog⟩
  unfold upperSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i _hi

  -- `i` is explicitly passed
  have hstep := upperStep_integrand_add_le_core P i hfAbove hgAbove

  -- Reconstruct the SourceHypotheses on the fly using the pieces in your context!
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core P ⟨_hab, hfAbove, _hfBelow, _hmono⟩

  have hmul := mul_le_mul_of_nonneg_right hstep hinc
  nlinarith

theorem lowerSum_integrand_add_le_core {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    lowerSum P f alpha + lowerSum P g alpha ≤
      lowerSum P (fun x => f x + g x) alpha := by
  -- For lower sums, we need the `BddBelow` pieces!
  rcases hsf with ⟨_hab, _hfAbove, hfBelow, _hmono⟩
  rcases hsg with ⟨_habg, _hgAbove, hgBelow, _hmonog⟩
  unfold lowerSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i _hi

  -- Apply the lowerStep lemma we fixed earlier
  have hstep := lowerStep_integrand_add_le_core P i hfBelow hgBelow

  -- Reconstruct the SourceHypotheses for the increment proof
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) := by
    exact partition_increment_nonneg_of_source_core P
      ⟨_hab, _hfAbove, hfBelow, _hmono⟩

  -- Multiply the step inequality by the non-negative increment width
  have hmul := mul_le_mul_of_nonneg_right hstep hinc
  nlinarith

lemma lowerStep_le_upperStep_core {a b : ℝ} (P : Partition a b)
    {f : ℝ → ℝ} (i : Fin P.n)
    (hBelow : BddBelow (f '' Set.Icc a b))
    (hAbove : BddAbove (f '' Set.Icc a b)) :
    lowerStep P f i ≤ upperStep P f i := by
  have hcell_nonempty : (f '' Partition.subinterval P i).Nonempty := by
    -- We show the image is non-empty by plugging in the left endpoint
    refine ⟨f (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc, ⟨le_rfl, le_of_lt (P.strict_mono (Fin.castSucc_lt_succ))⟩, rfl⟩

  have hcellBelow : BddBelow (f '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hBelow

  have hcellAbove : BddAbove (f '' Partition.subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hAbove

  rcases hcell_nonempty with ⟨y, hy⟩
  unfold lowerStep upperStep

  -- inf(f) ≤ y and y ≤ sup(f), therefore inf(f) ≤ sup(f)
  exact le_trans (csInf_le hcellBelow hy) (le_csSup hcellAbove hy)

theorem lowerSum_le_upperSum_core {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) :
    lowerSum P f alpha ≤ upperSum P f alpha := by
  -- Keep a copy of `hs` so we can extract bounds without destroying the original
  have hs_copy := hs
  rcases hs_copy with ⟨_hab, hAbove, hBelow, _hmono⟩

  unfold lowerSum upperSum
  refine Finset.sum_le_sum ?_
  intro i _hi  -- _hi is `i ∈ Finset.univ`, which we ignore

  -- 1. Prove the step inequality: m_i ≤ M_i
  have hstep := lowerStep_le_upperStep_core P i hBelow hAbove

  -- 2. Prove the increment is non-negative: 0 ≤ Δα_i
  -- We can just pass the intact `hs` directly!
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core P hs

  -- 3. Multiply them together: m_i * Δα_i ≤ M_i * Δα_i
  exact mul_le_mul_of_nonneg_right hstep hinc

theorem upperLowerCommonLimit_integrand_add_core {a b : ℝ} {f g alpha : ℝ → ℝ}
    {Lf Lg : ℝ}
    (hf : UpperLowerCommonLimit a b f alpha Lf)
    (hg : UpperLowerCommonLimit a b g alpha Lg) :
    UpperLowerCommonLimit a b (fun x => f x + g x) alpha (Lf + Lg) := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨hsg, hlimg⟩
  refine ⟨sourceHypotheses_integrand_add hsf hsg, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro P hmesh
  have hmeshf : P.mesh < δf := lt_of_lt_of_le hmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hmesh (min_le_right δf δg)
  have hPf := Hf P hmeshf
  have hPg := Hg P hmeshg
  have hsumUpper :
      upperSum P (fun x => f x + g x) alpha ≤
        upperSum P f alpha + upperSum P g alpha :=
    upperSum_integrand_add_le_core P hsf hsg
  have hsumLower :
      lowerSum P f alpha + lowerSum P g alpha ≤
        lowerSum P (fun x => f x + g x) alpha :=
    lowerSum_integrand_add_le_core P hsf hsg
  have hlowerUpper :
      lowerSum P (fun x => f x + g x) alpha ≤
        upperSum P (fun x => f x + g x) alpha :=
    lowerSum_le_upperSum_core P (sourceHypotheses_integrand_add hsf hsg)
  constructor
  · apply abs_lt.mpr
    constructor
    · have hf_low : Lf - lowerSum P f alpha < eps / 2 := by
        have hle : Lf - lowerSum P f alpha ≤ |lowerSum P f alpha - Lf| := by
          linarith [neg_le_abs (lowerSum P f alpha - Lf)]
        exact lt_of_le_of_lt hle hPf.2
      have hg_low : Lg - lowerSum P g alpha < eps / 2 := by
        have hle : Lg - lowerSum P g alpha ≤ |lowerSum P g alpha - Lg| := by
          linarith [neg_le_abs (lowerSum P g alpha - Lg)]
        exact lt_of_le_of_lt hle hPg.2
      have hbound :
          (Lf + Lg) - upperSum P (fun x => f x + g x) alpha ≤
            (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) := by
        linarith
      have hlt :
          (Lf + Lg) - upperSum P (fun x => f x + g x) alpha < eps := by
        have hsum : (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) <
            eps / 2 + eps / 2 := add_lt_add hf_low hg_low
        linarith
      linarith
    · have hf_up : upperSum P f alpha - Lf < eps / 2 := by
        have hle : upperSum P f alpha - Lf ≤ |upperSum P f alpha - Lf| := le_abs_self _
        exact lt_of_le_of_lt hle hPf.1
      have hg_up : upperSum P g alpha - Lg < eps / 2 := by
        have hle : upperSum P g alpha - Lg ≤ |upperSum P g alpha - Lg| := le_abs_self _
        exact lt_of_le_of_lt hle hPg.1
      have hbound :
          upperSum P (fun x => f x + g x) alpha - (Lf + Lg) ≤
            (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) := by
        linarith
      have hlt :
          upperSum P (fun x => f x + g x) alpha - (Lf + Lg) < eps := by
        have hsum : (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) <
            eps / 2 + eps / 2 := add_lt_add hf_up hg_up
        linarith
      exact hlt
  · apply abs_lt.mpr
    constructor
    · have hf_low : Lf - lowerSum P f alpha < eps / 2 := by
        have hle : Lf - lowerSum P f alpha ≤ |lowerSum P f alpha - Lf| := by
          linarith [neg_le_abs (lowerSum P f alpha - Lf)]
        exact lt_of_le_of_lt hle hPf.2
      have hg_low : Lg - lowerSum P g alpha < eps / 2 := by
        have hle : Lg - lowerSum P g alpha ≤ |lowerSum P g alpha - Lg| := by
          linarith [neg_le_abs (lowerSum P g alpha - Lg)]
        exact lt_of_le_of_lt hle hPg.2
      have hbound :
          (Lf + Lg) - lowerSum P (fun x => f x + g x) alpha ≤
            (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) := by
        linarith
      have hlt :
          (Lf + Lg) - lowerSum P (fun x => f x + g x) alpha < eps := by
        have hsum : (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) <
            eps / 2 + eps / 2 := add_lt_add hf_low hg_low
        linarith
      linarith
    · have hf_up : upperSum P f alpha - Lf < eps / 2 := by
        have hle : upperSum P f alpha - Lf ≤ |upperSum P f alpha - Lf| := le_abs_self _
        exact lt_of_le_of_lt hle hPf.1
      have hg_up : upperSum P g alpha - Lg < eps / 2 := by
        have hle : upperSum P g alpha - Lg ≤ |upperSum P g alpha - Lg| := le_abs_self _
        exact lt_of_le_of_lt hle hPg.1
      have hbound :
          lowerSum P (fun x => f x + g x) alpha - (Lf + Lg) ≤
            (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) := by
        linarith
      have hlt :
          lowerSum P (fun x => f x + g x) alpha - (Lf + Lg) < eps := by
        have hsum : (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) <
            eps / 2 + eps / 2 := add_lt_add hf_up hg_up
        linarith
      exact hlt

lemma abs_const_mul_error_lt_core {c old L eps : ℝ}
    (heps : 0 < eps) (hold : |old - L| < eps / (|c| + 1)) :
    |c * (old - L)| < eps := by
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rw [abs_mul]
  have hmul₁ : |c| * |old - L| ≤ |c| * (eps / C) :=
    mul_le_mul_of_nonneg_left (le_of_lt (by simpa [C] using hold)) (abs_nonneg c)
  have hmul₂ : |c| * (eps / C) < C * (eps / C) := by
    dsimp [C]
    exact mul_lt_mul_of_pos_right (lt_add_one |c|) hscale
  have hCmul : C * (eps / C) = eps := by
    field_simp [ne_of_gt hCpos]
  exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)

lemma image_const_mul_subinterval_eq_smul_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) :
    (fun x => c * f x) '' Partition.subinterval P i = c • (f '' Partition.subinterval P i) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [smul_eq_mul]⟩

lemma upperStep_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : 0 ≤ c) :
    upperStep P (fun x => c * f x) i = c * upperStep P f i := by
  unfold upperStep
  rw [image_const_mul_subinterval_eq_smul_core]
  -- `Real.sSup_smul_of_nonneg` proves sup(c • S) = c • sup(S) when c ≥ 0
  simpa [smul_eq_mul] using Real.sSup_smul_of_nonneg hc (f '' Partition.subinterval P i)

theorem upperSum_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : 0 ≤ c) :
    upperSum P (fun x => c * f x) alpha = c * upperSum P f alpha := by
  unfold upperSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [upperStep_const_mul_nonneg_core P f i hc]
  ring

lemma lowerStep_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : 0 ≤ c) :
    lowerStep P (fun x => c * f x) i = c * lowerStep P f i := by
  unfold lowerStep
  rw [image_const_mul_subinterval_eq_smul_core]
  -- `Real.sInf_smul_of_nonneg` proves inf(c • S) = c • inf(S) when c ≥ 0
  simpa [smul_eq_mul] using Real.sInf_smul_of_nonneg hc (f '' Partition.subinterval P i)

theorem lowerSum_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : 0 ≤ c) :
    lowerSum P (fun x => c * f x) alpha = c * lowerSum P f alpha := by
  unfold lowerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [lowerStep_const_mul_nonneg_core P f i hc]
  ring

lemma upperStep_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : c ≤ 0) :
    upperStep P (fun x => c * f x) i = c * lowerStep P f i := by
  unfold upperStep lowerStep
  rw [image_const_mul_subinterval_eq_smul_core]
  -- `Real.sSup_smul_of_nonpos` proves sup(c • S) = c • inf(S) when c ≤ 0
  simpa [smul_eq_mul] using Real.sSup_smul_of_nonpos hc (f '' Partition.subinterval P i)

theorem upperSum_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : c ≤ 0) :
    upperSum P (fun x => c * f x) alpha = c * lowerSum P f alpha := by
  unfold upperSum lowerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [upperStep_const_mul_nonpos_core P f i hc]
  ring

lemma lowerStep_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : c ≤ 0) :
    lowerStep P (fun x => c * f x) i = c * upperStep P f i := by
  unfold lowerStep upperStep
  rw [image_const_mul_subinterval_eq_smul_core]
  -- `Real.sInf_smul_of_nonpos` proves inf(c • S) = c • sup(S) when c ≤ 0
  simpa [smul_eq_mul] using Real.sInf_smul_of_nonpos hc (f '' Partition.subinterval P i)

theorem lowerSum_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : c ≤ 0) :
    lowerSum P (fun x => c * f x) alpha = c * upperSum P f alpha := by
  unfold lowerSum upperSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [lowerStep_const_mul_nonpos_core P f i hc]
  ring

theorem upperLowerCommonLimit_const_mul_core {a b c : ℝ} {f alpha : ℝ → ℝ}
    {L : ℝ}
    (h : UpperLowerCommonLimit a b f alpha L) :
    UpperLowerCommonLimit a b (fun x => c * f x) alpha (c * L) := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_const_mul_core hs, ?_⟩
  intro eps heps
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rcases hlim (eps / C) hscale with ⟨δ, hδ, H⟩
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh
  have hP := H P hmesh
  by_cases hc : 0 ≤ c
  · constructor
    · have hEq :
          upperSum P (fun x => c * f x) alpha - c * L =
            c * (upperSum P f alpha - L) := by
        rw [upperSum_const_mul_nonneg_core P f alpha hc]
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.1)
    · have hEq :
          lowerSum P (fun x => c * f x) alpha - c * L =
            c * (lowerSum P f alpha - L) := by
        rw [lowerSum_const_mul_nonneg_core P f alpha hc]
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.2)
  · have hc' : c ≤ 0 := le_of_not_ge hc
    constructor
    · have hEq :
          upperSum P (fun x => c * f x) alpha - c * L =
            c * (lowerSum P f alpha - L) := by
        rw [upperSum_const_mul_nonpos_core P f alpha hc']
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.2)
    · have hEq :
          lowerSum P (fun x => c * f x) alpha - c * L =
            c * (upperSum P f alpha - L) := by
        rw [lowerSum_const_mul_nonpos_core P f alpha hc']
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.1)

theorem taggedSum_const_mul_core {a b c : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (f alpha : ℝ → ℝ) :
    taggedSum P tags (fun x => c * f x) alpha = c * taggedSum P tags f alpha := by
  unfold taggedSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem taggedCommonLimit_const_mul_core {a b c : ℝ} {f alpha : ℝ → ℝ}
    {L : ℝ}
    (h : TaggedCommonLimit a b f alpha L) :
    TaggedCommonLimit a b (fun x => c * f x) alpha (c * L) := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_const_mul_core hs, ?_⟩
  intro eps heps
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rcases hlim (eps / C) hscale with ⟨δ, hδ, H⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh
  have hP := H P tags htags hmesh
  have hEq :
      taggedSum P tags (fun x => c * f x) alpha - c * L =
        c * (taggedSum P tags f alpha - L) := by
    rw [taggedSum_const_mul_core]
    ring
  rw [hEq, abs_mul]
  have hmul₁ : |c| * |taggedSum P tags f alpha - L| ≤
      |c| * (eps / C) :=
    mul_le_mul_of_nonneg_left (le_of_lt hP) (abs_nonneg c)
  have hmul₂ : |c| * (eps / C) < C * (eps / C) := by
    dsimp [C]
    exact mul_lt_mul_of_pos_right (lt_add_one |c|) hscale
  have hCmul : C * (eps / C) = eps := by
    field_simp [ne_of_gt hCpos]
  exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)

lemma tag_mem_Icc_of_tagsInPartition_core {a b : ℝ} (P : Partition a b)
    {tags : Fin P.n → ℝ} (htags : tagsInPartition P tags)
    (i : Fin P.n) :
    tags i ∈ Set.Icc a b :=
  -- `htags i` proves the tag is in the subinterval.
  -- `subinterval_subset_Icc_core` applies the subset property.
  subinterval_subset_Icc_core P (htags i)

theorem taggedSum_mono_core {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    {f g alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (htags : tagsInPartition P tags)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    taggedSum P tags f alpha ≤ taggedSum P tags g alpha := by
  unfold taggedSum
  refine Finset.sum_le_sum ?_
  intro i _hi

  -- 1. Prove the tag is inside [a, b]
  have htag : tags i ∈ Set.Icc a b := tag_mem_Icc_of_tagsInPartition_core P htags i

  -- 2. Evaluate the function inequality at the tag
  have hstep : f (tags i) ≤ g (tags i) := hfg (tags i) htag

  -- 3. The increment is non-negative (pass `hs` directly!)
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core P hs

  -- 4. Multiply the step inequality by the non-negative increment
  exact mul_le_mul_of_nonneg_right hstep hinc

theorem taggedCommonLimit_mono_core {a b : ℝ} {f g alpha : ℝ → ℝ} {Lf Lg : ℝ}
    (hf : TaggedCommonLimit a b f alpha Lf)
    (hg : TaggedCommonLimit a b g alpha Lg)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    Lf ≤ Lg := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨_hsg, hlimg⟩

  -- Create a copy of `hsf` so we can extract `hab` without destroying `hsf`
  have hsf_copy := hsf
  rcases hsf_copy with ⟨hab, _hAbove, _hBelow, _hmono⟩

  rw [le_iff_forall_pos_lt_add]
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  rcases exists_partition_mesh_lt hab (lt_min hδf hδg) with ⟨P, hPmesh⟩

  -- FIX: Define `tags` to exactly match `Fin P.n → ℝ` using left endpoints
  let tags : Fin P.n → ℝ := fun i => P.pts i.castSucc

  -- We already proved this earlier!
  have htags : tagsInPartition P tags := leftTagsInPartition P

  have hmeshf : P.mesh < δf := lt_of_lt_of_le hPmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hPmesh (min_le_right δf δg)
  have hPf := Hf P tags htags hmeshf
  have hPg := Hg P tags htags hmeshg

  -- Pass `hsf` cleanly without rebuilding it!
  have hsum : taggedSum P tags f alpha ≤ taggedSum P tags g alpha :=
    taggedSum_mono_core P tags hsf htags hfg

  have hf_bound : Lf < taggedSum P tags f alpha + eps / 2 := by
    have hleft := (abs_lt.mp hPf).1
    linarith
  have hg_bound : taggedSum P tags g alpha < Lg + eps / 2 := by
    have hright := (abs_lt.mp hPg).2
    linarith
  linarith

theorem taggedSum_between_lower_upper_core {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    lowerSum P f alpha ≤ taggedSum P tags f alpha ∧
      taggedSum P tags f alpha ≤ upperSum P f alpha := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  constructor
  · unfold lowerSum taggedSum
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hcellBelow : BddBelow (f '' Partition.subinterval P i) :=
      BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hBelow
    have hlow_le_tag : lowerStep P f i ≤ f (tags i) := by
      unfold lowerStep
      exact csInf_le hcellBelow ⟨tags i, htags i, rfl⟩
    have hinc_nonneg :
        0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
      partition_increment_nonneg_of_source_core P
        ⟨hab, hAbove, hBelow, hmono⟩
    exact mul_le_mul_of_nonneg_right hlow_le_tag hinc_nonneg
  · unfold taggedSum upperSum
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hcellAbove : BddAbove (f '' Partition.subinterval P i) :=
      BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hAbove
    have htag_le_up : f (tags i) ≤ upperStep P f i := by
      unfold upperStep
      exact le_csSup hcellAbove ⟨tags i, htags i, rfl⟩
    have hinc_nonneg :
        0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
      partition_increment_nonneg_of_source_core P
        ⟨hab, hAbove, hBelow, hmono⟩
    exact mul_le_mul_of_nonneg_right htag_le_up hinc_nonneg

theorem taggedBridgeObligation {a b : ℝ} {f alpha : ℝ → ℝ} {L : ℝ}
    (hUL : UpperLowerCommonLimit a b f alpha L) :
    TaggedCommonLimit a b f alpha L := by
  rcases hUL with ⟨hs, hlim⟩
  refine ⟨hs, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P tags htags hmesh
  have hP := Hdelta P hmesh
  have hbetween := taggedSum_between_lower_upper_core hs P tags htags
  have hlower_abs := abs_lt.mp hP.2
  have hupper_abs := abs_lt.mp hP.1
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end DarbouxRS

theorem taggedCommonLimit_of_upperLowerCommonLimit {f alpha : ℝ → ℝ} {a b L : ℝ}
    (hUL : rsUpperLowerCommonLimit a b f alpha L) :
    rsTaggedCommonLimit a b f alpha L :=
  DarbouxRS.taggedBridgeObligation hUL

theorem rsIntegral_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsTaggedCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  taggedCommonLimit_of_upperLowerCommonLimit (rsIntegral_source_spec h)

theorem rsIntegral_source_and_tagged_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsUpperLowerCommonLimit a b f alpha (rsIntegral f alpha a b h) ∧
      rsTaggedCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  ⟨rsIntegral_source_spec h, rsIntegral_spec h⟩

noncomputable def rsIntegralWitness_integrand_add {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b) :
    RSIntegralWitness (fun x => f x + g x) alpha a b where
  value := rsIntegral f alpha a b hf + rsIntegral g alpha a b hg
  source_limit :=
    DarbouxRS.upperLowerCommonLimit_integrand_add_core
      (rsIntegral_source_spec hf) (rsIntegral_source_spec hg)

noncomputable def rsIntegrable_integrand_add {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b) :
    RSIntegrable (fun x => f x + g x) alpha a b :=
  (rsIntegralWitness_integrand_add hf hg).toRSIntegrable

theorem rsIntegral_integrand_add {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b) :
    rsIntegral (fun x => f x + g x) alpha a b
        (rsIntegrable_integrand_add hf hg) =
      rsIntegral f alpha a b hf + rsIntegral g alpha a b hg := by
  exact DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_integrand_add hf hg))
    (DarbouxRS.taggedCommonLimit_integrand_add (rsIntegral_spec hf) (rsIntegral_spec hg))

noncomputable def rsIntegralWitness_integrand_const_mul {f alpha : ℝ → ℝ} {c a b : ℝ}
    (hf : RSIntegrable f alpha a b) :
    RSIntegralWitness (fun x => c * f x) alpha a b where
  value := c * rsIntegral f alpha a b hf
  source_limit :=
    DarbouxRS.upperLowerCommonLimit_const_mul_core
      (c := c) (rsIntegral_source_spec hf)

noncomputable def rsIntegrable_integrand_const_mul {f alpha : ℝ → ℝ} {c a b : ℝ}
    (hf : RSIntegrable f alpha a b) :
    RSIntegrable (fun x => c * f x) alpha a b :=
  (rsIntegralWitness_integrand_const_mul (c := c) hf).toRSIntegrable

theorem rsIntegral_integrand_const_mul {f alpha : ℝ → ℝ} {c a b : ℝ}
    (hf : RSIntegrable f alpha a b) :
    rsIntegral (fun x => c * f x) alpha a b
        (rsIntegrable_integrand_const_mul (c := c) hf) =
      c * rsIntegral f alpha a b hf := by
  exact DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_integrand_const_mul (c := c) hf))
    (DarbouxRS.taggedCommonLimit_const_mul_core (c := c) (rsIntegral_spec hf))

theorem rsIntegral_integrand_mono {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    rsIntegral f alpha a b hf ≤ rsIntegral g alpha a b hg :=
  DarbouxRS.taggedCommonLimit_mono_core (rsIntegral_spec hf) (rsIntegral_spec hg) hfg

noncomputable def rsIntegralWitness_integrator_add {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
    RSIntegralWitness f (fun x => α₁ x + α₂ x) a b where
  value := rsIntegral f α₁ a b h₁ + rsIntegral f α₂ a b h₂
  source_limit :=
    DarbouxRS.upperLowerCommonLimit_integrator_add
      (rsIntegral_source_spec h₁) (rsIntegral_source_spec h₂)

noncomputable def rsIntegrable_integrator_add {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
    RSIntegrable f (fun x => α₁ x + α₂ x) a b :=
  (rsIntegralWitness_integrator_add h₁ h₂).toRSIntegrable

theorem rsIntegral_integrator_add {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
    rsIntegral f (fun x => α₁ x + α₂ x) a b (rsIntegrable_integrator_add h₁ h₂) =
      rsIntegral f α₁ a b h₁ + rsIntegral f α₂ a b h₂ := by
  exact DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_integrator_add h₁ h₂))
    (DarbouxRS.taggedCommonLimit_integrator_add (rsIntegral_spec h₁) (rsIntegral_spec h₂))
