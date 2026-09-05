/-
TASK ID: def_6_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic










open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]



noncomputable def simpleFunctionIntegralTerm
    (μ : Measure Ω) (X : SimpleFunc Ω EReal) (x : EReal) : EReal :=
  x * (μ (X ⁻¹' {x}) : EReal)



def simpleFunctionHasPosInf (μ : Measure Ω) (X : SimpleFunc Ω EReal)
  : Prop :=
  ∃ x ∈ X.range, simpleFunctionIntegralTerm μ X x = ⊤



def simpleFunctionHasNegInf (μ : Measure Ω) (X : SimpleFunc Ω EReal) : Prop :=
  ∃ x ∈ X.range, simpleFunctionIntegralTerm μ X x = ⊥



def simpleFunctionIntegralDefined (μ : Measure Ω) (X : SimpleFunc Ω EReal) : Prop :=
  ¬ (simpleFunctionHasPosInf μ X ∧ simpleFunctionHasNegInf μ X)



noncomputable def simpleFunctionIntegralValue
  (μ : Measure Ω) (X : SimpleFunc Ω EReal) : EReal :=
  Finset.sum X.range fun x => simpleFunctionIntegralTerm μ X x



noncomputable def def_6_2 (μ : Measure Ω) (X : SimpleFunc Ω EReal) : Option EReal :=
  by
    classical
    exact
      if h : simpleFunctionIntegralDefined μ X then
        some (simpleFunctionIntegralValue μ X)
      else
        none

 
theorem ereal_coe_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ENNReal) :
    ((∑ i ∈ s, f i : ENNReal) : EReal) = ∑ i ∈ s, ((f i : ENNReal) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp [ha, ih]



theorem integralValue_map (μ : Measure Ω) {β : Type*}
    (g : β → EReal) (f : SimpleFunc Ω β) :
    simpleFunctionIntegralValue μ (f.map g) =
      ∑ x ∈ f.range, g x * (μ (f ⁻¹' {x}) : EReal) := by
  classical
  simp only [simpleFunctionIntegralValue, SimpleFunc.range_map]
  refine Finset.sum_image' _ fun b hb => ?_
  rcases SimpleFunc.mem_range.1 hb with ⟨a, rfl⟩
  simp only [simpleFunctionIntegralTerm]
  rw [SimpleFunc.map_preimage_singleton]
  have hsum :
      ((μ (f ⁻¹' ↑({b ∈ f.range | g b = g (f a)})) : ENNReal) : EReal) =
        ∑ y ∈ f.range.filter (fun y => g y = g (f a)), ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
    rw [← f.sum_measure_preimage_singleton (s := f.range.filter fun y => g y = g (f a)),
      ereal_coe_finset_sum]
  let s : Finset β := f.range.filter fun y => g y = g (f a)
  have hdist :
      g (f a) * ∑ y ∈ s, ((μ (f ⁻¹' {y}) : ENNReal) : EReal) =
        ∑ y ∈ s, g (f a) * ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
    classical
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert y s hy ih =>
        rw [Finset.sum_insert hy, Finset.sum_insert hy]
        have hy_nonneg : 0 ≤ ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
          positivity
        have hs_nonneg : 0 ≤ ∑ z ∈ s, ((μ (f ⁻¹' {z}) : ENNReal) : EReal) := by
          positivity
        rw [EReal.left_distrib_of_nonneg hy_nonneg hs_nonneg, ih]
  have hsum_mul :
      g (f a) * (μ (f ⁻¹' ↑({b ∈ f.range | g b = g (f a)})) : EReal) =
        g (f a) * ∑ y ∈ f.range.filter (fun y => g y = g (f a)),
          ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
    exact congrArg (fun t : EReal => g (f a) * t) hsum
  have hdist' :
      g (f a) * ∑ y ∈ f.range.filter (fun y => g y = g (f a)),
          ((μ (f ⁻¹' {y}) : ENNReal) : EReal) =
        ∑ y ∈ f.range.filter (fun y => g y = g (f a)),
          g (f a) * ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
    simpa [s] using hdist
  have hpointwise :
      ∑ y ∈ f.range.filter (fun y => g y = g (f a)),
          g (f a) * ((μ (f ⁻¹' {y}) : ENNReal) : EReal) =
        ∑ y ∈ f.range.filter (fun y => g y = g (f a)),
          g y * ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
    refine Finset.sum_congr rfl ?_
    intro y hy
    rw [(Finset.mem_filter.1 hy).2]
  simpa using hsum_mul.trans (hdist'.trans hpointwise)



theorem integralValue_mono_fun (μ : Measure Ω) {f g : SimpleFunc Ω EReal} (hfg : f ≤ g) :
    simpleFunctionIntegralValue μ f ≤ simpleFunctionIntegralValue μ g := by
  classical
  calc
    simpleFunctionIntegralValue μ f
        = simpleFunctionIntegralValue μ ((f.pair g).map Prod.fst) := by
            simp
    _ = ∑ x ∈ (f.pair g).range, x.1 * (μ (f.pair g ⁻¹' {x}) : EReal) := by
          rw [integralValue_map (μ := μ) (g := Prod.fst)]
    _ ≤ ∑ x ∈ (f.pair g).range, x.2 * (μ (f.pair g ⁻¹' {x}) : EReal) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          have hxle : x.1 ≤ x.2 := by
            rcases SimpleFunc.mem_range.1 hx with ⟨ω, rfl⟩
            exact hfg ω
          have hμnonneg : 0 ≤ (μ (f.pair g ⁻¹' {x}) : EReal) := by
            positivity
          exact mul_le_mul_of_nonneg_right hxle hμnonneg
    _ = simpleFunctionIntegralValue μ ((f.pair g).map Prod.snd) := by
          rw [integralValue_map (μ := μ) (g := Prod.snd)]
    _ = simpleFunctionIntegralValue μ g := by
          simp

 
theorem def62_eq_some_iff (μ : Measure Ω) (f : SimpleFunc Ω EReal) (v : EReal) :
    def_6_2 μ f = some v ↔
      simpleFunctionIntegralDefined μ f ∧ simpleFunctionIntegralValue μ f = v := by
  classical
  unfold def_6_2
  by_cases h : simpleFunctionIntegralDefined μ f
  · simp [h]
  · simp [h]



def textbookERealAddDefined (x y : EReal) : Prop :=
  ¬ ((x = ⊤ ∧ y = ⊥) ∨ (x = ⊥ ∧ y = ⊤))

 
noncomputable def textbookERealAdd (x y : EReal) : Option EReal := by
  classical
  exact
    if h : textbookERealAddDefined x y then
      some (x + y)
    else
      none

 
noncomputable def textbookIntegralAdd (u v : Option EReal) : Option EReal := by
  classical
  exact
    match u, v with
    | some x, some y => textbookERealAdd x y
    | _, _ => none



def simpleFunctionIntegralAddCompatible (μ : Measure Ω)
    (X Y : SimpleFunc Ω EReal) : Prop :=
  ∀ p ∈ (X.pair Y).range,
    (p.1 + p.2) * (μ (X.pair Y ⁻¹' {p}) : EReal) =
      p.1 * (μ (X.pair Y ⁻¹' {p}) : EReal) +
        p.2 * (μ (X.pair Y ⁻¹' {p}) : EReal)



noncomputable def simpleFunctionIntegralAdd (μ : Measure Ω)
    (X Y : SimpleFunc Ω EReal) : Option EReal := by
  classical
  exact
    if h : simpleFunctionIntegralAddCompatible μ X Y then
      def_6_2 μ (X + Y)
    else
      none



noncomputable def textbookERealFinSum : (n : ℕ) → (Fin n → EReal) → Option EReal
  | 0, _ => some 0
  | n + 1, f => textbookIntegralAdd (some (f 0)) (textbookERealFinSum n fun i => f i.succ)

 
theorem textbookERealFinSum_zero (f : Fin 0 → EReal) :
    textbookERealFinSum 0 f = some 0 := by
  simp [textbookERealFinSum]

 
theorem textbookERealFinSum_succ (n : ℕ) (f : Fin (n + 1) → EReal) :
    textbookERealFinSum (n + 1) f =
      textbookIntegralAdd (some (f 0)) (textbookERealFinSum n fun i => f i.succ) := by
  simp [textbookERealFinSum]

 
theorem textbookERealFinSum_one (f : Fin 1 → EReal) :
    textbookERealFinSum 1 f = some (f 0) := by
  rw [textbookERealFinSum_succ, textbookERealFinSum_zero]
  simp [textbookIntegralAdd, textbookERealAdd, textbookERealAddDefined]



noncomputable def simpleFunctionIntegralFinChain (μ : Measure Ω) :
    (n : ℕ) → (Fin n → SimpleFunc Ω EReal) → Option EReal
  | 0, _ => some 0
  | n + 1, F =>
      match simpleFunctionIntegralFinChain μ n (fun i => F i.succ) with
      | some _ => simpleFunctionIntegralAdd μ (F 0) (∑ i : Fin n, F i.succ)
      | none => none

 
theorem simpleFunctionIntegralFinChain_zero (μ : Measure Ω) (F : Fin 0 → SimpleFunc Ω EReal) :
    simpleFunctionIntegralFinChain μ 0 F = some 0 := by
  simp [simpleFunctionIntegralFinChain]

 
theorem simpleFunctionIntegralFinChain_succ (μ : Measure Ω) (n : ℕ)
    (F : Fin (n + 1) → SimpleFunc Ω EReal) :
    simpleFunctionIntegralFinChain μ (n + 1) F =
      match simpleFunctionIntegralFinChain μ n (fun i => F i.succ) with
      | some _ => simpleFunctionIntegralAdd μ (F 0) (∑ i : Fin n, F i.succ)
      | none => none := by
  simp [simpleFunctionIntegralFinChain]



noncomputable def indicatorRepresentationSummand
    (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω) :
    Fin n → SimpleFunc Ω EReal :=
  fun i => (SimpleFunc.const Ω (b i)).restrict (B i)



noncomputable def indicatorRepresentationSimpleFunction
    (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω) : SimpleFunc Ω EReal :=
  ∑ i : Fin n, indicatorRepresentationSummand (Ω := Ω) n b B i



noncomputable def indicatorRepresentationWeightedSum
    (μ : Measure Ω) (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω) : Option EReal :=
  textbookERealFinSum n fun i => b i * (μ (B i) : EReal)



noncomputable def indicatorRepresentationIntegral
    (μ : Measure Ω) (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω) : Option EReal :=
  simpleFunctionIntegralFinChain μ n (indicatorRepresentationSummand (Ω := Ω) n b B)



noncomputable def indicatorRepresentationIntegralChain
    (μ : Measure Ω) (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω) : Option EReal :=
  indicatorRepresentationIntegral (Ω := Ω) μ n b B

 
theorem indicatorRepresentationSimpleFunction_succ
    (n : ℕ) (b : Fin (n + 1) → EReal) (B : Fin (n + 1) → Set Ω) :
    indicatorRepresentationSimpleFunction (Ω := Ω) (n + 1) b B =
      indicatorRepresentationSummand (Ω := Ω) (n + 1) b B 0 +
        indicatorRepresentationSimpleFunction (Ω := Ω) n (fun i => b i.succ) (fun i => B i.succ) := by
  simp [indicatorRepresentationSimpleFunction, indicatorRepresentationSummand, Fin.sum_univ_succ]

 
theorem indicatorRepresentationWeightedSum_succ (μ : Measure Ω)
    (n : ℕ) (b : Fin (n + 1) → EReal) (B : Fin (n + 1) → Set Ω) :
    indicatorRepresentationWeightedSum (Ω := Ω) μ (n + 1) b B =
      textbookIntegralAdd
        (some (b 0 * (μ (B 0) : EReal)))
        (indicatorRepresentationWeightedSum (Ω := Ω) μ n (fun i => b i.succ) (fun i => B i.succ)) := by
  simp [indicatorRepresentationWeightedSum, textbookERealFinSum_succ]

 
theorem indicatorRepresentationIntegral_succ (μ : Measure Ω)
    (n : ℕ) (b : Fin (n + 1) → EReal) (B : Fin (n + 1) → Set Ω) :
    indicatorRepresentationIntegral (Ω := Ω) μ (n + 1) b B =
      match indicatorRepresentationIntegral (Ω := Ω) μ n (fun i => b i.succ) (fun i => B i.succ) with
      | some _ =>
          simpleFunctionIntegralAdd μ
            (indicatorRepresentationSummand (Ω := Ω) (n + 1) b B 0)
            (indicatorRepresentationSimpleFunction (Ω := Ω) n (fun i => b i.succ) (fun i => B i.succ))
      | none => none := by
  congr! 2

 
theorem indicatorRepresentationIntegralChain_succ (μ : Measure Ω)
    (n : ℕ) (b : Fin (n + 1) → EReal) (B : Fin (n + 1) → Set Ω) :
    indicatorRepresentationIntegralChain (Ω := Ω) μ (n + 1) b B =
      match indicatorRepresentationIntegralChain (Ω := Ω) μ n (fun i => b i.succ) (fun i => B i.succ) with
      | some _ =>
          simpleFunctionIntegralAdd μ
            (indicatorRepresentationSummand (Ω := Ω) (n + 1) b B 0)
            (indicatorRepresentationSimpleFunction (Ω := Ω) n (fun i => b i.succ) (fun i => B i.succ))
      | none => none := by
  simpa [indicatorRepresentationIntegralChain] using
    (indicatorRepresentationIntegral_succ (Ω := Ω) (μ := μ) (n := n) (b := b) (B := B))




---------------------------
-- Connection to Mathlib
---------------------------





theorem not_simpleFunctionHasNegInf_map_ennreal
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    ¬ simpleFunctionHasNegInf μ (X.map fun x : ENNReal => (x : EReal)) := by
  classical
  rintro ⟨x, hx_range, hx_bot⟩
  -- it is the coercion of some `ENNReal`, hence nonnegative.
  have hx_nonneg : 0 ≤ x := by
    rcases SimpleFunc.mem_range.1 hx_range with ⟨a, rfl⟩
    change (0 : EReal) ≤ ((X a : ENNReal) : EReal)
    exact_mod_cast (show (0 : ENNReal) ≤ X a from zero_le)

  -- The measure factor is also nonnegative.
  have hμ_nonneg :
      0 ≤ ((μ ((X.map fun x : ENNReal => (x : EReal)) ⁻¹' {x}) : ENNReal) : EReal) := by
    positivity

  -- Hence the corresponding summand is nonnegative.
  have hterm_nonneg :
      0 ≤ simpleFunctionIntegralTerm μ
          (X.map fun x : ENNReal => (x : EReal)) x := by
    unfold simpleFunctionIntegralTerm
    exact mul_nonneg hx_nonneg hμ_nonneg

  -- But `⊥ < 0`, so a nonnegative term cannot be `⊥`.
  have hbot_lt_zero : (⊥ : EReal) < 0 := by
    exact EReal.bot_lt_coe 0

  have hnot : ¬ simpleFunctionIntegralTerm μ
          (X.map fun x : ENNReal => (x : EReal)) x ≤ ⊥ := by
    intro hle
    exact not_le_of_gt hbot_lt_zero (le_trans hterm_nonneg hle)

  exact hnot (le_of_eq hx_bot)




theorem simpleFunctionIntegralDefined_map_ennreal
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    simpleFunctionIntegralDefined μ (X.map fun x : ENNReal => (x : EReal)) := by
  -- By definition of `simpleFunctionIntegralDefined`, we need to show that if `X.map (fun x => x : ENNReal → EReal)` has a positive infinite term, it cannot have a negative infinite term.
  unfold simpleFunctionIntegralDefined
  intro h_contra
  obtain ⟨x, hx⟩ := h_contra;
  convert not_simpleFunctionHasNegInf_map_ennreal μ X hx using 1



theorem simpleFunctionIntegralValue_map_ennreal_eq_lintegral
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    simpleFunctionIntegralValue μ (X.map fun x : ENNReal => (x : EReal)) =
      ((X.lintegral μ : ENNReal) : EReal) := by
  classical
  calc
    simpleFunctionIntegralValue μ (X.map fun x : ENNReal => (x : EReal))
        =
          ∑ x ∈ X.range,
            (x : EReal) * (μ (X ⁻¹' {x}) : EReal) := by
          simpa using
            integralValue_map μ (fun x : ENNReal => (x : EReal)) X
    _ =
        ((∑ x ∈ X.range, x * μ (X ⁻¹' {x}) : ENNReal) : EReal) := by
          rw [ereal_coe_finset_sum]
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact_mod_cast
            (show x * μ (X ⁻¹' {x}) = x * μ (X ⁻¹' {x}) from rfl)
    _ =
        ((X.lintegral μ : ENNReal) : EReal) := by
          rfl




theorem def_6_2_map_ennreal_eq_lintegral
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    def_6_2 μ (X.map fun x : ENNReal => (x : EReal)) =
      some ((X.lintegral μ : ENNReal) : EReal) := by
  classical
  unfold def_6_2
  simp [
    simpleFunctionIntegralDefined_map_ennreal μ X,
    simpleFunctionIntegralValue_map_ennreal_eq_lintegral μ X
  ]
