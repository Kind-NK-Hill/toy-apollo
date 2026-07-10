import Mathlib
import ToyApollo.Output.def_2_4
import ToyApollo.Output.thm_2_1

open Filter Set

noncomputable section

/-- Sequence A from problem 2.7(a): A(0) = ∅, A(n+1) = [1/(n+1), 4+(-1)^(n+1)] -/
def prob_2_7_A : ℕ → Set ℝ := fun i =>
  match i with
  | 0 => ∅
  | n + 1 => Set.Icc (1 / (n + 1 : ℝ)) (4 + (-1 : ℝ) ^ (n + 1))

/-- Sequence B from problem 2.7(b): B(0) = ∅, B(n+1) = [0,1] if n+1 odd, [1,2] if n+1 even -/
def prob_2_7_B : ℕ → Set ℝ := fun i =>
  match i with
  | 0 => ∅
  | n + 1 => if (n + 1) % 2 = 1 then Set.Icc (0 : ℝ) 1 else Set.Icc (1 : ℝ) 2

/-
For part (a):
- For odd i: (-1)^i = -1, so A_i = [1/i, 3]
- For even i: (-1)^i = 1, so A_i = [1/i, 5]
- liminf = {x : x ∈ A_i for all but finitely many i} = (0, 3]
  * For 0 < x ≤ 3: eventually 1/i < x, and x ≤ 3 ≤ 4+(-1)^i for all i ≥ 1
  * For x ≤ 0: x < 1/i never in A_i
  * For x > 3: x > 3 = upper bound of odd-indexed sets, so fails infinitely often
- limsup = {x : x ∈ A_i for infinitely many i} = (0, 5]
  * For 0 < x ≤ 5: x ∈ A_i for all even i large enough (since A_i = [1/i, 5])
  * For x ≤ 0 or x > 5: never in any A_i

For part (b):
- liminf = {x : x ∈ B_i for all but finitely many i} = {1}
  * x=1 is in both [0,1] and [1,2]
  * Any other x is missing from infinitely many B_i
- limsup = {x : x ∈ B_i for infinitely many i} = [0, 2]
  * [0,1] appears for all odd i, [1,2] for all even i
-/
lemma prob_2_7_liminf_A : liminf prob_2_7_A atTop = Set.Ioc (0 : ℝ) 3 := by
  -- For x ∈ (0, 3], show that there exists N such that for all m ≥ N, x ∈ prob_2_7_A m.
  have h_inf : ∀ x, 0 < x ∧ x ≤ 3 → ∃ N, ∀ m ≥ N, x ∈ prob_2_7_A m := by
    simp [prob_2_7_A];
    intro x hx₁ hx₂; use Nat.ceil ( x⁻¹ ) + 1; intro m hm; rcases m with ( _ | _ | m ) <;> norm_num at *;
    · linarith;
    · exact ⟨ by rw [ inv_eq_one_div, div_le_iff₀ ] <;> nlinarith [ mul_inv_cancel₀ hx₁.ne' ], by cases' Nat.even_or_odd ( m + 1 + 1 ) with h h <;> rw [ h.neg_one_pow ] <;> linarith ⟩;
  -- For x ∈ liminf prob_2_7_A atTop, show that x ∈ (0, 3].
  have h_liminf : ∀ x, x ∈ liminf prob_2_7_A atTop → 0 < x ∧ x ≤ 3 := by
    simp +contextual [ Filter.liminf_eq, Filter.eventually_atTop ];
    intro x S N hS hx
    have hOdd := hS (2 * N + 1) (by linarith) hx
    have hEven := hS (2 * N + 2) (by linarith) hx
    norm_num [prob_2_7_A, pow_add, pow_mul] at hOdd hEven
    exact ⟨lt_of_lt_of_le (by positivity) hEven.1, by linarith [hOdd.2]⟩
  refine' Set.Subset.antisymm h_liminf fun x hx => _;
  obtain ⟨ N, hN ⟩ := h_inf x hx;
  exact ⟨ { x }, Filter.eventually_atTop.mpr ⟨ N, fun m hm => by aesop ⟩, by aesop ⟩

lemma prob_2_7_limsup_A : limsup prob_2_7_A atTop = Set.Ioc (0 : ℝ) 5 := by
  refine' le_antisymm _ _;
  · refine' sInf_le _;
    simp +zetaDelta at *;
    use 2;
    intro b hb; intro x hx; induction b <;> norm_num [ * ] at *;
    exact ⟨ lt_of_lt_of_le ( by positivity ) hx.1, hx.2.trans ( by linarith [ show ( -1 : ℝ ) ^ ( ‹_› + 1 ) ≤ 1 by exact le_of_abs_le ( by norm_num ) ] ) ⟩;
  · intro x hx; simp_all +decide [ Filter.limsup_eq_iInf_iSup ] ; (
    intro s n hs; rcases exists_nat_gt ( x⁻¹ ) with ⟨ m, hm ⟩ ; use 2 * ( n + m + 1 ) ; norm_num [ Nat.add_mod, Nat.mul_mod, prob_2_7_A ] at *;
    exact ⟨ hs _ ( by linarith ), ⟨ by rw [ inv_eq_one_div, div_le_iff₀ ] <;> norm_num <;> nlinarith [ mul_inv_cancel₀ hx.1.ne' ], by norm_num [ Nat.even_add_one ] ; linarith ⟩ ⟩);

lemma prob_2_7_liminf_B : liminf prob_2_7_B atTop = ({1} : Set ℝ) := by
  refine' Set.Subset.antisymm _ _;
  · intro x;
    simp +decide [ Filter.liminf_eq, Filter.eventually_atTop ];
    intro s n hs hx; have := hs ( 2 * n + 1 ) ( by linarith ) ; have := hs ( 2 * n + 2 ) ( by linarith ) ; norm_num [ Nat.add_mod, Nat.mul_mod, prob_2_7_B ] at *;
    linarith [ Set.mem_Icc.mp ( ‹s ⊆ Icc 0 1› hx ), Set.mem_Icc.mp ( ‹s ⊆ Icc 1 2› hx ) ];
  · simp +decide [ Set.subset_def, liminf_eq_iSup_iInf_of_nat ];
    use 1;
    intro i hi; unfold prob_2_7_B; aesop;

lemma prob_2_7_limsup_B : limsup prob_2_7_B atTop = Set.Icc (0 : ℝ) 2 := by
  ext x;
  simp +decide [ Filter.limsup_eq_iInf_iSup ];
  constructor;
  · intro hx;
    contrapose! hx;
    use { n | n ≥ 1 ∧ x ∉ prob_2_7_B n };
    use 1;
    unfold prob_2_7_B;
    grind;
  · intro hx i n hn;
    by_cases h : x ≤ 1;
    · exact ⟨ 2 * n + 1, hn _ ( by linarith ), by unfold prob_2_7_B; norm_num; constructor <;> linarith ⟩;
    · use 2 * n + 2;
      exact ⟨ hn _ ( by linarith ), by unfold prob_2_7_B; norm_num [ Nat.add_mod, Nat.mul_mod ] ; constructor <;> linarith ⟩

/--
PROBLEM
\textbf{2.7.} Find the limits superior and inferior of the following sequences of sets.
-/
theorem prob_2_7 :
    let A : ℕ → Set ℝ := fun i =>
      match i with
      | 0 => ∅
      | n+1 => Set.Icc (1 / (n+1 : ℝ)) (4 + (-1 : ℝ) ^ (n+1))
    let B : ℕ → Set ℝ := fun i =>
      match i with
      | 0 => ∅
      | n+1 => if (n+1) % 2 = 1 then Set.Icc (0 : ℝ) 1 else Set.Icc (1 : ℝ) 2
    (liminf A atTop = Set.Ioc (0 : ℝ) 3 ∧ limsup A atTop = Set.Ioc (0 : ℝ) 5) ∧
    (liminf B atTop = ({1} : Set ℝ) ∧ limsup B atTop = Set.Icc (0 : ℝ) 2) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- A and prob_2_7_A are the same
    change liminf prob_2_7_A atTop = Set.Ioc (0 : ℝ) 3
    exact prob_2_7_liminf_A
  · change limsup prob_2_7_A atTop = Set.Ioc (0 : ℝ) 5
    exact prob_2_7_limsup_A
  · change liminf prob_2_7_B atTop = ({1} : Set ℝ)
    exact prob_2_7_liminf_B
  · change limsup prob_2_7_B atTop = Set.Icc (0 : ℝ) 2
    exact prob_2_7_limsup_B
