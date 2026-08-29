/-
TASK ID: ex_8_3_4
TYPE: Example_Proof
SOURCE PLAN: 33_chap8_monge_kantorovich
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open scoped BigOperators

noncomputable section

abbrev Ex834Source := Bool

abbrev Ex834Target := Fin 3

def ex834Plan : Ex834Source → Ex834Target → ℝ
  | false, 0 => 1 / 5
  | false, 1 => 1 / 15
  | false, 2 => 1 / 15
  | true, 0 => 0
  | true, 1 => 2 / 15
  | true, 2 => 8 / 15

def ex834TransportCost (c : Ex834Source → Ex834Target → ℝ)
    (T : Ex834Source → Ex834Target → ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * T i j

def IsEx834FeasiblePlan (T : Ex834Source → Ex834Target → ℝ) : Prop :=
  (∀ i j, 0 ≤ T i j) ∧
    (∑ j, T false j = 1 / 3) ∧
    (∑ j, T true j = 2 / 3) ∧
    (∑ i, T i 0 = 1 / 5) ∧
    (∑ i, T i 1 = 1 / 5) ∧
    (∑ i, T i 2 = 3 / 5)

def IsEx834OptimalPlan (c : Ex834Source → Ex834Target → ℝ)
    (T : Ex834Source → Ex834Target → ℝ) : Prop :=
  IsEx834FeasiblePlan T ∧
    ∀ S, IsEx834FeasiblePlan S →
      ex834TransportCost c T ≤ ex834TransportCost c S

theorem ex834Plan_feasible : IsEx834FeasiblePlan ex834Plan := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases j <;> cases i <;> norm_num [ex834Plan]
  · rw [Fin.sum_univ_three]
    norm_num [ex834Plan]
  · rw [Fin.sum_univ_three]
    norm_num [ex834Plan]
  · norm_num [ex834Plan, Fintype.sum_bool]
  · norm_num [ex834Plan, Fintype.sum_bool]
  · norm_num [ex834Plan, Fintype.sum_bool]

private theorem continuous_ex834_apply (i : Ex834Source) (j : Ex834Target) :
    Continuous (fun T : Ex834Source → Ex834Target → ℝ => T i j) := by
  fun_prop

private theorem isClosed_ex834FeasiblePlan :
    IsClosed {T : Ex834Source → Ex834Target → ℝ | IsEx834FeasiblePlan T} := by
  have hnonneg :
      IsClosed {T : Ex834Source → Ex834Target → ℝ | ∀ i j, 0 ≤ T i j} := by
    rw [show {T : Ex834Source → Ex834Target → ℝ | ∀ i j, 0 ≤ T i j} =
        ⋂ i, ⋂ j, {T | 0 ≤ T i j} by ext T; simp]
    exact isClosed_iInter fun i =>
      isClosed_iInter fun j =>
        isClosed_le continuous_const (continuous_ex834_apply i j)
  have hrowFalse :
      IsClosed {T : Ex834Source → Ex834Target → ℝ |
        ∑ j, T false j = 1 / 3} :=
    isClosed_eq (by fun_prop) continuous_const
  have hrowTrue :
      IsClosed {T : Ex834Source → Ex834Target → ℝ |
        ∑ j, T true j = 2 / 3} :=
    isClosed_eq (by fun_prop) continuous_const
  have hcolZero :
      IsClosed {T : Ex834Source → Ex834Target → ℝ |
        ∑ i, T i 0 = 1 / 5} :=
    isClosed_eq (by fun_prop) continuous_const
  have hcolOne :
      IsClosed {T : Ex834Source → Ex834Target → ℝ |
        ∑ i, T i 1 = 1 / 5} :=
    isClosed_eq (by fun_prop) continuous_const
  have hcolTwo :
      IsClosed {T : Ex834Source → Ex834Target → ℝ |
        ∑ i, T i 2 = 3 / 5} :=
    isClosed_eq (by fun_prop) continuous_const
  simpa only [IsEx834FeasiblePlan, Set.setOf_and] using
    hnonneg.inter
      (hrowFalse.inter
        (hrowTrue.inter
          (hcolZero.inter (hcolOne.inter hcolTwo))))

private theorem isCompact_ex834FeasiblePlan :
    IsCompact {T : Ex834Source → Ex834Target → ℝ | IsEx834FeasiblePlan T} := by
  let feasible :=
    {T : Ex834Source → Ex834Target → ℝ | IsEx834FeasiblePlan T}
  let cube : Set (Ex834Source → Ex834Target → ℝ) := Set.Icc 0 1
  have hsubset : feasible ⊆ cube := by
    intro T hT
    constructor
    · intro i j
      exact hT.1 i j
    · intro i j
      have hcoord : T i j ≤ ∑ k, T i k :=
        Finset.single_le_sum (fun k _ => hT.1 i k) (Finset.mem_univ j)
      cases i with
      | false =>
          calc
            T false j ≤ ∑ k, T false k := hcoord
            _ = 1 / 3 := hT.2.1
            _ ≤ 1 := by norm_num
      | true =>
          calc
            T true j ≤ ∑ k, T true k := hcoord
            _ = 2 / 3 := hT.2.2.1
            _ ≤ 1 := by norm_num
  have hcube : IsCompact cube := isCompact_Icc
  have heq : feasible = cube ∩ feasible := by
    ext T
    constructor
    · intro hT
      exact ⟨hsubset hT, hT⟩
    · intro hT
      exact hT.2
  rw [show {T : Ex834Source → Ex834Target → ℝ |
      IsEx834FeasiblePlan T} = feasible by rfl, heq]
  exact hcube.inter_right isClosed_ex834FeasiblePlan

private theorem continuous_ex834TransportCost
    (c : Ex834Source → Ex834Target → ℝ) :
    Continuous (ex834TransportCost c) := by
  unfold ex834TransportCost
  fun_prop

theorem ex_8_3_4 :
    ∀ c : Ex834Source → Ex834Target → ℝ,
      ∃ T, IsEx834OptimalPlan c T := by
  intro c
  let feasible :=
    {T : Ex834Source → Ex834Target → ℝ | IsEx834FeasiblePlan T}
  have hnonempty : feasible.Nonempty := ⟨ex834Plan, ex834Plan_feasible⟩
  obtain ⟨T, hT, hmin⟩ :=
    isCompact_ex834FeasiblePlan.exists_isMinOn hnonempty
      (continuous_ex834TransportCost c).continuousOn
  exact ⟨T, hT, fun _ hS => hmin hS⟩

namespace Ex834FiniteWasserstein

structure FiniteProbabilityLaw (X : Type*) [Fintype X] where
  mass : X → ℝ
  mass_nonneg : ∀ x, 0 ≤ mass x
  sum_mass : ∑ x, mass x = 1

def IsFiniteCoupling {X : Type*} [Fintype X]
    (P Q : FiniteProbabilityLaw X) (μ : X → X → ℝ) : Prop :=
  (∀ x y, 0 ≤ μ x y) ∧
    (∀ x, ∑ y, μ x y = P.mass x) ∧
    (∀ y, ∑ x, μ x y = Q.mass y)

def metricPowerCost {X : Type*} [MetricSpace X]
    (p : ℝ) (x y : X) : ℝ :=
  Real.rpow (dist x y) p

def finiteCouplingCost {X : Type*} [Fintype X] [MetricSpace X]
    (p : ℝ) (μ : X → X → ℝ) : ℝ :=
  ∑ x, ∑ y, metricPowerCost p x y * μ x y

def finiteMinimumCouplingCost {X : Type*} [Fintype X] [MetricSpace X]
    (P Q : FiniteProbabilityLaw X) (p : ℝ) : ℝ :=
  sInf {r | ∃ μ, IsFiniteCoupling P Q μ ∧ finiteCouplingCost p μ = r}

def finitePWasserstein {X : Type*} [Fintype X] [MetricSpace X]
    (P Q : FiniteProbabilityLaw X) (p : ℝ) (_hp : 1 ≤ p) : ℝ :=
  Real.rpow (finiteMinimumCouplingCost P Q p) p⁻¹

private def productCoupling {X : Type*} [Fintype X]
    (P Q : FiniteProbabilityLaw X) : X → X → ℝ :=
  fun x y => P.mass x * Q.mass y

private theorem productCoupling_isFiniteCoupling {X : Type*} [Fintype X]
    (P Q : FiniteProbabilityLaw X) :
    IsFiniteCoupling P Q (productCoupling P Q) := by
  refine ⟨fun x y => mul_nonneg (P.mass_nonneg x) (Q.mass_nonneg y), ?_, ?_⟩
  · intro x
    rw [show (∑ y, productCoupling P Q x y) =
        P.mass x * ∑ y, Q.mass y by simp [productCoupling, Finset.mul_sum]]
    rw [Q.sum_mass, mul_one]
  · intro y
    rw [show (∑ x, productCoupling P Q x y) =
        (∑ x, P.mass x) * Q.mass y by simp [productCoupling, Finset.sum_mul]]
    rw [P.sum_mass, one_mul]

private theorem continuous_finiteCoupling_apply
    {X : Type*} [Fintype X] (x y : X) :
    Continuous (fun μ : X → X → ℝ => μ x y) := by
  fun_prop

private theorem isClosed_finiteCouplings
    {X : Type*} [Fintype X] (P Q : FiniteProbabilityLaw X) :
    IsClosed {μ : X → X → ℝ | IsFiniteCoupling P Q μ} := by
  have hnonneg :
      IsClosed {μ : X → X → ℝ | ∀ x y, 0 ≤ μ x y} := by
    rw [show {μ : X → X → ℝ | ∀ x y, 0 ≤ μ x y} =
        ⋂ x, ⋂ y, {μ | 0 ≤ μ x y} by ext μ; simp]
    exact isClosed_iInter fun x =>
      isClosed_iInter fun y =>
        isClosed_le continuous_const (continuous_finiteCoupling_apply x y)
  have hfirst :
      IsClosed {μ : X → X → ℝ | ∀ x, ∑ y, μ x y = P.mass x} := by
    rw [show {μ : X → X → ℝ | ∀ x, ∑ y, μ x y = P.mass x} =
        ⋂ x, {μ | ∑ y, μ x y = P.mass x} by ext μ; simp]
    exact isClosed_iInter fun _ => isClosed_eq (by fun_prop) continuous_const
  have hsecond :
      IsClosed {μ : X → X → ℝ | ∀ y, ∑ x, μ x y = Q.mass y} := by
    rw [show {μ : X → X → ℝ | ∀ y, ∑ x, μ x y = Q.mass y} =
        ⋂ y, {μ | ∑ x, μ x y = Q.mass y} by ext μ; simp]
    exact isClosed_iInter fun _ => isClosed_eq (by fun_prop) continuous_const
  simpa only [IsFiniteCoupling, Set.setOf_and] using
    hnonneg.inter (hfirst.inter hsecond)

private theorem isCompact_finiteCouplings
    {X : Type*} [Fintype X] (P Q : FiniteProbabilityLaw X) :
    IsCompact {μ : X → X → ℝ | IsFiniteCoupling P Q μ} := by
  let couplings := {μ : X → X → ℝ | IsFiniteCoupling P Q μ}
  let cube : Set (X → X → ℝ) :=
    {μ | ∀ x y, μ x y ∈ Set.Icc (0 : ℝ) 1}
  have hsubset : couplings ⊆ cube := by
    intro μ hμ
    intro x y
    constructor
    · exact hμ.1 x y
    · calc
        μ x y ≤ ∑ z, μ x z :=
          Finset.single_le_sum (fun z _ => hμ.1 x z) (Finset.mem_univ y)
        _ = P.mass x := hμ.2.1 x
        _ ≤ ∑ z, P.mass z :=
          Finset.single_le_sum (fun z _ => P.mass_nonneg z) (Finset.mem_univ x)
        _ = 1 := P.sum_mass
  have hcube : IsCompact cube := by
    exact isCompact_pi_infinite fun _ =>
      isCompact_pi_infinite fun _ => isCompact_Icc
  have heq : couplings = cube ∩ couplings := by
    ext μ
    constructor
    · intro hμ
      exact ⟨hsubset hμ, hμ⟩
    · intro hμ
      exact hμ.2
  rw [show {μ : X → X → ℝ | IsFiniteCoupling P Q μ} = couplings by rfl, heq]
  exact hcube.inter_right (isClosed_finiteCouplings P Q)

private theorem continuous_finiteCouplingCost
    {X : Type*} [Fintype X] [MetricSpace X] (p : ℝ) :
    Continuous (finiteCouplingCost (X := X) p) := by
  unfold finiteCouplingCost metricPowerCost
  fun_prop

private theorem finiteCouplingCost_nonneg
    {X : Type*} [Fintype X] [MetricSpace X]
    {P Q : FiniteProbabilityLaw X} {p : ℝ} {μ : X → X → ℝ}
    (hμ : IsFiniteCoupling P Q μ) :
    0 ≤ finiteCouplingCost p μ := by
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (Real.rpow_nonneg dist_nonneg p) (hμ.1 x y)

theorem finitePWasserstein_exists_minimizer
    {X : Type*} [Fintype X] [MetricSpace X]
    (P Q : FiniteProbabilityLaw X) (p : ℝ) (hp : 1 ≤ p) :
    ∃ μ, IsFiniteCoupling P Q μ ∧
      (∀ ν, IsFiniteCoupling P Q ν →
        finiteCouplingCost p μ ≤ finiteCouplingCost p ν) ∧
      finiteMinimumCouplingCost P Q p = finiteCouplingCost p μ ∧
      finitePWasserstein P Q p hp =
        Real.rpow (finiteCouplingCost p μ) p⁻¹ := by
  let couplings := {μ : X → X → ℝ | IsFiniteCoupling P Q μ}
  have hnonempty : couplings.Nonempty :=
    ⟨productCoupling P Q, productCoupling_isFiniteCoupling P Q⟩
  obtain ⟨μ, hμ, hmin⟩ :=
    (isCompact_finiteCouplings P Q).exists_isMinOn hnonempty
      (continuous_finiteCouplingCost (X := X) p).continuousOn
  have hcosts_nonempty :
      ({r | ∃ ν, IsFiniteCoupling P Q ν ∧ finiteCouplingCost p ν = r} :
        Set ℝ).Nonempty :=
    ⟨finiteCouplingCost p μ, μ, hμ, rfl⟩
  have hcosts_bdd :
      BddBelow {r | ∃ ν, IsFiniteCoupling P Q ν ∧ finiteCouplingCost p ν = r} := by
    refine ⟨0, ?_⟩
    rintro r ⟨ν, hν, rfl⟩
    exact finiteCouplingCost_nonneg hν
  have hminimum :
      finiteMinimumCouplingCost P Q p = finiteCouplingCost p μ := by
    apply le_antisymm
    · exact csInf_le hcosts_bdd ⟨μ, hμ, rfl⟩
    · exact le_csInf hcosts_nonempty fun r hr => by
        obtain ⟨ν, hν, rfl⟩ := hr
        exact hmin hν
  refine ⟨μ, hμ, fun ν hν => hmin hν, hminimum, ?_⟩
  unfold finitePWasserstein
  rw [hminimum]

end Ex834FiniteWasserstein
