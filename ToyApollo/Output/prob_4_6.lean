import Mathlib

open Set
open MeasureTheory

noncomputable section

private def prob46Cell (n : ℤ) : Set ℝ := Set.Ioc (n : ℝ) (n + 1)

private def prob46Index (x : ℝ) : ℤ := Int.ceil x - 1

private def prob46Union (S : Set ℤ) : Set ℝ := ⋃ n ∈ S, prob46Cell n

private lemma prob46_mem_cell_iff (x : ℝ) (n : ℤ) : x ∈ prob46Cell n ↔ prob46Index x = n := by
  constructor
  · intro hx
    have h1 : n < Int.ceil x := by
      exact Int.lt_ceil.mpr hx.1
    have h2 : Int.ceil x ≤ n + 1 := by
      exact Int.ceil_le.mpr (by simpa using hx.2)
    have hceil : Int.ceil x = n + 1 := by
      omega
    unfold prob46Index
    omega
  · intro hx
    have hceil : Int.ceil x = n + 1 := by
      unfold prob46Index at hx
      omega
    constructor
    · exact Int.lt_ceil.mp (by simp [hceil])
    · have hle : Int.ceil x ≤ n + 1 := by simp [hceil]
      simpa using (Int.ceil_le.mp hle)

private lemma prob46_mem_union_iff (x : ℝ) (S : Set ℤ) : x ∈ prob46Union S ↔ prob46Index x ∈ S := by
  constructor
  · intro hx
    rcases mem_iUnion.1 hx with ⟨n, hx⟩
    rcases mem_iUnion.1 hx with ⟨hnS, hxn⟩
    have hxeq : prob46Index x = n := (prob46_mem_cell_iff x n).1 hxn
    simpa [hxeq] using hnS
  · intro hx
    refine mem_iUnion.2 ?_
    refine ⟨prob46Index x, ?_⟩
    refine mem_iUnion.2 ?_
    exact ⟨hx, (prob46_mem_cell_iff x (prob46Index x)).2 rfl⟩

private lemma prob46_measurableSet_iff (A : Set ℝ) :
    @MeasurableSet ℝ (MeasurableSpace.comap prob46Index ⊤) A ↔ ∃ S : Set ℤ, A = prob46Union S := by
  constructor
  · intro hA
    rcases hA with ⟨S, _, hS⟩
    refine ⟨S, ?_⟩
    ext x
    rw [← hS, prob46_mem_union_iff]
    rfl
  · rintro ⟨S, rfl⟩
    refine ⟨S, ?_, ?_⟩
    · trivial
    · ext x
      rw [prob46_mem_union_iff]
      rfl

theorem prob_4_6 :
    let mG : MeasurableSpace ℝ := MeasurableSpace.comap prob46Index ⊤
    (∀ A : Set ℝ, @MeasurableSet ℝ mG A ↔ ∃ S : Set ℤ, A = prob46Union S) ∧
      ∀ f : ℝ → ℝ, @Measurable ℝ ℝ mG (borel ℝ) f →
        ∀ n : ℤ, ∀ x y : ℝ, x ∈ prob46Cell n → y ∈ prob46Cell n → f x = f y := by
  dsimp
  constructor
  · intro A
    exact prob46_measurableSet_iff A
  · intro f hf n x y hx hy
    have hxphi : prob46Index x = n := (prob46_mem_cell_iff x n).1 hx
    have hyphi : prob46Index y = n := (prob46_mem_cell_iff y n).1 hy
    by_contra hne
    have hmeas : @MeasurableSet ℝ (MeasurableSpace.comap prob46Index ⊤) (f ⁻¹' ({f x} : Set ℝ)) :=
      hf (MeasurableSet.singleton (f x))
    rcases (prob46_measurableSet_iff (f ⁻¹' ({f x} : Set ℝ))).1 hmeas with ⟨S, hS⟩
    have hxmem : x ∈ prob46Union S := by
      rw [← hS]
      simp
    have hphiS : prob46Index x ∈ S := (prob46_mem_union_iff x S).1 hxmem
    have hymem : y ∈ prob46Union S := (prob46_mem_union_iff y S).2 (by simpa [hxphi, hyphi] using hphiS)
    have hyfx : y ∈ f ⁻¹' ({f x} : Set ℝ) := by
      rw [hS]
      exact hymem
    have : f y = f x := by
      simpa using hyfx
    exact hne this.symm
