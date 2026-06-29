import ToyApollo.Output.prob_14_1_asymptotic_support

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal Asymptotics

noncomputable section

/-- Full source-level setup for Problem 14.1.

The setup carries only the urn parameters and the Beta law data.  The finite
white-count laws are derived below from the parent-owned finite Polya path law,
not supplied as arbitrary public setup data. -/
structure prob_14_1_PolyaUrnBetaSetup where
  w : ℝ
  b : ℝ
  w_pos : 0 < w
  b_pos : 0 < b

namespace prob_14_1_PolyaUrnBetaSetup

/-- The limiting law is not a public premise: it is the standard beta law
canonically determined by the source urn parameters. -/
def beta (S : prob_14_1_PolyaUrnBetaSetup) :
    prob_14_1_BetaLawData S.w S.b :=
  prob_14_1_standardBetaLawData S.w_pos S.b_pos

end prob_14_1_PolyaUrnBetaSetup


/- The former fixed-path obligation is represented by
`prob_14_1_path_probability_product`; no `obl_*` facade is kept here. -/

open scoped BigOperators

/-- A finite color path for Polya-urn draws. `true` denotes a white draw and
`false` denotes a black draw. -/
abbrev prob_14_1_ColorPath := List Bool

/-- Number of white draws in a finite color path. -/
def prob_14_1_whiteDrawCount : prob_14_1_ColorPath → ℕ
  | [] => 0
  | true :: rest => prob_14_1_whiteDrawCount rest + 1
  | false :: rest => prob_14_1_whiteDrawCount rest

/-- Number of black draws in a finite color path. -/
def prob_14_1_blackDrawCount : prob_14_1_ColorPath → ℕ
  | [] => 0
  | true :: rest => prob_14_1_blackDrawCount rest
  | false :: rest => prob_14_1_blackDrawCount rest + 1

/-- The set of white draw positions in a fixed-length color path represented
as a function on `Fin i`. -/
def prob_14_1_finWhiteSet {i : ℕ} (path : Fin i → Bool) : Finset (Fin i) :=
  Finset.univ.filter fun j => path j = true

/-- Number of white draws in a fixed-length function-path. -/
def prob_14_1_finWhiteCount {i : ℕ} (path : Fin i → Bool) : ℕ :=
  (prob_14_1_finWhiteSet path).card

/-- A fixed-length path has at most one white draw at each index. -/
theorem prob_14_1_finWhiteCount_le_length {i : ℕ}
    (path : Fin i → Bool) :
    prob_14_1_finWhiteCount path ≤ i := by
  rw [prob_14_1_finWhiteCount, prob_14_1_finWhiteSet]
  simpa [Fintype.card_fin] using
    (Finset.card_le_univ (prob_14_1_finWhiteSet path))

/-- Fixed-length boolean paths with exactly `k` white draws are equivalent to
`k`-element subsets of their index set. -/
noncomputable def prob_14_1_finPathWhiteSetEquiv (i k : ℕ) :
    {path : Fin i → Bool // prob_14_1_finWhiteCount path = k} ≃
      {s : Finset (Fin i) //
        s ∈ Finset.powersetCard k (Finset.univ : Finset (Fin i))} where
  toFun p := by
    refine ⟨prob_14_1_finWhiteSet p.1, ?_⟩
    rw [Finset.mem_powersetCard]
    constructor
    · intro x _hx
      exact Finset.mem_univ x
    · simpa [prob_14_1_finWhiteCount] using p.2
  invFun s := by
    refine ⟨(fun j : Fin i => decide (j ∈ s.1)), ?_⟩
    have hfilter :
        prob_14_1_finWhiteSet (fun j : Fin i => decide (j ∈ s.1)) = s.1 := by
      ext j
      simp [prob_14_1_finWhiteSet]
    have hcard : s.1.card = k := (Finset.mem_powersetCard.mp s.2).2
    simp [prob_14_1_finWhiteCount, hfilter, hcard]
  left_inv p := by
    apply Subtype.ext
    funext j
    cases h : p.1 j <;> simp [prob_14_1_finWhiteSet, h]
  right_inv s := by
    apply Subtype.ext
    ext j
    simp [prob_14_1_finWhiteSet]

/-- There are `Nat.choose i k` fixed-length color paths with exactly `k` white
draws.  This is the combinatorial counting factor in the beta-binomial mass
formula; it does not assert the mass formula itself. -/
theorem prob_14_1_fin_path_white_count_card (i k : ℕ) :
    Fintype.card {path : Fin i → Bool // prob_14_1_finWhiteCount path = k} =
      Nat.choose i k := by
  calc
    Fintype.card {path : Fin i → Bool // prob_14_1_finWhiteCount path = k}
        = Fintype.card
            {s : Finset (Fin i) //
              s ∈ Finset.powersetCard k (Finset.univ : Finset (Fin i))} :=
          Fintype.card_congr (prob_14_1_finPathWhiteSetEquiv i k)
    _ = (Finset.powersetCard k (Finset.univ : Finset (Fin i))).card := by
          exact Fintype.card_coe
            (Finset.powersetCard k (Finset.univ : Finset (Fin i)))
    _ = Nat.choose i k := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- Finset-cardinality version of the fixed-length path-counting theorem. -/
theorem prob_14_1_card_filter_fin_paths_white_count (i k : ℕ) :
    (Finset.univ.filter
      (fun path : Fin i → Bool => prob_14_1_finWhiteCount path = k)).card =
      Nat.choose i k := by
  rw [← prob_14_1_fin_path_white_count_card i k]
  have hcard := Fintype.card_ofFinset
    (p := {path : Fin i → Bool | prob_14_1_finWhiteCount path = k})
    (s := Finset.univ.filter
      (fun path : Fin i → Bool => prob_14_1_finWhiteCount path = k))
    (by intro f; simp)
  exact hcard.symm

/-- Summing a constant over all fixed-length paths with `k` white positions
produces the binomial coefficient factor. -/
theorem prob_14_1_sum_constant_over_fin_paths_white_count
    (i k : ℕ) (c : ℝ) :
    (Finset.univ.filter
      (fun path : Fin i → Bool => prob_14_1_finWhiteCount path = k)).sum
        (fun _ : Fin i → Bool => c) =
      (Nat.choose i k : ℝ) * c := by
  rw [Finset.sum_const, nsmul_eq_mul,
    prob_14_1_card_filter_fin_paths_white_count]

/-- The one-step conditional probability after a prefix with `white` white
draws and `black` black draws. -/
def prob_14_1_polyaPathStepProbabilityFrom
    (w b : ℝ) (white black : ℕ) (color : Bool) : ℝ :=
  match color with
  | true => (w + (white : ℝ)) / (b + w + ((white + black : ℕ) : ℝ))
  | false => (b + (black : ℝ)) / (b + w + ((white + black : ℕ) : ℝ))

/-- Recursive finite-path mass generated by the Polya transition rule.  This is
the local path-law object; it is not defined as the target product. -/
def prob_14_1_polyaPathMassFrom (w b : ℝ) : ℕ → ℕ → prob_14_1_ColorPath → ℝ
  | _, _, [] => 1
  | white, black, true :: rest =>
      prob_14_1_polyaPathStepProbabilityFrom w b white black true *
        prob_14_1_polyaPathMassFrom w b (white + 1) black rest
  | white, black, false :: rest =>
      prob_14_1_polyaPathStepProbabilityFrom w b white black false *
        prob_14_1_polyaPathMassFrom w b white (black + 1) rest

/-- The explicit list of stepwise Polya transition factors along a path. -/
def prob_14_1_polyaPathStepFactorsFrom
    (w b : ℝ) : ℕ → ℕ → prob_14_1_ColorPath → List ℝ
  | _, _, [] => []
  | white, black, true :: rest =>
      prob_14_1_polyaPathStepProbabilityFrom w b white black true ::
        prob_14_1_polyaPathStepFactorsFrom w b (white + 1) black rest
  | white, black, false :: rest =>
      prob_14_1_polyaPathStepProbabilityFrom w b white black false ::
        prob_14_1_polyaPathStepFactorsFrom w b white (black + 1) rest

/-- Recursive path mass equals the product of the generated step factors. -/
theorem prob_14_1_polyaPathMassFrom_eq_stepFactors_prod
    (w b : ℝ) :
    ∀ (white black : ℕ) (path : prob_14_1_ColorPath),
      prob_14_1_polyaPathMassFrom w b white black path =
        (prob_14_1_polyaPathStepFactorsFrom w b white black path).prod := by
  intro white black path
  induction path generalizing white black with
  | nil =>
      simp [prob_14_1_polyaPathMassFrom, prob_14_1_polyaPathStepFactorsFrom]
  | cons color rest ih =>
      cases color <;>
        simp [prob_14_1_polyaPathMassFrom, prob_14_1_polyaPathStepFactorsFrom, ih]

/-- The sequential mass assigned to a fixed finite Polya color path. -/
def prob_14_1_polyaPathProbability
    (w b : ℝ) (path : prob_14_1_ColorPath) : ℝ :=
  prob_14_1_polyaPathMassFrom w b 0 0 path

/-- The stepwise urn probabilities encountered along a fixed finite path. -/
def prob_14_1_polyaPathStepFactors
    (w b : ℝ) (path : prob_14_1_ColorPath) : List ℝ :=
  prob_14_1_polyaPathStepFactorsFrom w b 0 0 path

/-- Fixed-path probability is the product of the stepwise urn probabilities.
This is the focused path-probability spine; it does not sum over paths or prove
the beta-binomial mass formula. -/
theorem prob_14_1_path_probability_product
    (w b : ℝ) (path : prob_14_1_ColorPath) :
    prob_14_1_polyaPathProbability w b path =
      (prob_14_1_polyaPathStepFactors w b path).prod := by
  simpa [prob_14_1_polyaPathProbability, prob_14_1_polyaPathStepFactors]
    using prob_14_1_polyaPathMassFrom_eq_stepFactors_prod w b 0 0 path

/-- Along any finite color path, the white and black draw counts add to the
path length.  This is the count algebra needed before summing path masses by
white-count fibers. -/
theorem prob_14_1_white_black_count_add_length
    (path : prob_14_1_ColorPath) :
    prob_14_1_whiteDrawCount path + prob_14_1_blackDrawCount path =
      path.length := by
  induction path with
  | nil =>
      simp [prob_14_1_whiteDrawCount, prob_14_1_blackDrawCount]
  | cons color rest ih =>
      cases color <;>
        simp [prob_14_1_whiteDrawCount, prob_14_1_blackDrawCount] <;> omega

/-- Closed form for the recursive path mass from an arbitrary current urn
state.  The numerator records only how many future white/black draws occur;
the denominator records the deterministic total-ball sequence. -/
theorem prob_14_1_polyaPathMassFrom_count_formula_inv
    (w b : ℝ) :
    ∀ (white black : ℕ) (path : prob_14_1_ColorPath),
      prob_14_1_polyaPathMassFrom w b white black path =
        prob_14_1_risingFactorial (w + white)
            (prob_14_1_whiteDrawCount path) *
          prob_14_1_risingFactorial (b + black)
            (prob_14_1_blackDrawCount path) *
          (prob_14_1_risingFactorial
            (b + w + (white + black : ℕ)) path.length)⁻¹ := by
  intro white black path
  induction path generalizing white black with
  | nil =>
      simp [prob_14_1_polyaPathMassFrom, prob_14_1_risingFactorial,
        prob_14_1_whiteDrawCount, prob_14_1_blackDrawCount]
  | cons color rest ih =>
      cases color
      · rw [prob_14_1_polyaPathMassFrom, ih]
        simp [prob_14_1_polyaPathStepProbabilityFrom,
          prob_14_1_whiteDrawCount, prob_14_1_blackDrawCount,
          prob_14_1_risingFactorial_succ_left, div_eq_mul_inv]
        ring_nf
      · rw [prob_14_1_polyaPathMassFrom, ih]
        simp [prob_14_1_polyaPathStepProbabilityFrom,
          prob_14_1_whiteDrawCount, prob_14_1_blackDrawCount,
          prob_14_1_risingFactorial_succ_left, div_eq_mul_inv]
        ring_nf

/-- Division-form version of the fixed-path mass formula. -/
theorem prob_14_1_polyaPathMassFrom_count_formula
    (w b : ℝ) :
    ∀ (white black : ℕ) (path : prob_14_1_ColorPath),
      prob_14_1_polyaPathMassFrom w b white black path =
        (prob_14_1_risingFactorial (w + white)
            (prob_14_1_whiteDrawCount path) *
          prob_14_1_risingFactorial (b + black)
            (prob_14_1_blackDrawCount path)) /
          prob_14_1_risingFactorial
            (b + w + (white + black : ℕ)) path.length := by
  intro white black path
  rw [prob_14_1_polyaPathMassFrom_count_formula_inv]
  rw [div_eq_mul_inv]

/-- Fixed-path probability depends only on the number of white and black draws,
not on their order. -/
theorem prob_14_1_polyaPathProbability_eq_count_formula
    (w b : ℝ) (path : prob_14_1_ColorPath) :
    prob_14_1_polyaPathProbability w b path =
      (prob_14_1_risingFactorial w (prob_14_1_whiteDrawCount path) *
        prob_14_1_risingFactorial b (prob_14_1_blackDrawCount path)) /
        prob_14_1_risingFactorial (b + w) path.length := by
  simpa [prob_14_1_polyaPathProbability] using
    prob_14_1_polyaPathMassFrom_count_formula w b 0 0 path

/-- Every finite path has nonnegative recursive mass when the current urn
state has positive initial white and black masses. -/
theorem prob_14_1_polyaPathMassFrom_nonneg {w b : ℝ}
    (hw : 0 < w) (hb : 0 < b)
    (white black : ℕ) (path : prob_14_1_ColorPath) :
    0 ≤ prob_14_1_polyaPathMassFrom w b white black path := by
  rw [prob_14_1_polyaPathMassFrom_count_formula]
  have hw_state : 0 < w + white := by
    exact add_pos_of_pos_of_nonneg hw (by exact_mod_cast Nat.zero_le white)
  have hb_state : 0 < b + black := by
    exact add_pos_of_pos_of_nonneg hb (by exact_mod_cast Nat.zero_le black)
  have hden_pos :
      0 < prob_14_1_risingFactorial
        (b + w + ((white + black : ℕ) : ℝ)) path.length := by
    refine prob_14_1_risingFactorial_pos_of_pos ?_ path.length
    have hcount : 0 ≤ ((white + black : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le (white + black)
    nlinarith
  exact div_nonneg
    (mul_nonneg
      (prob_14_1_risingFactorial_pos_of_pos hw_state
        (prob_14_1_whiteDrawCount path)).le
      (prob_14_1_risingFactorial_pos_of_pos hb_state
        (prob_14_1_blackDrawCount path)).le)
    hden_pos.le

/-- Every finite Polya path probability is nonnegative. -/
theorem prob_14_1_polyaPathProbability_nonneg {w b : ℝ}
    (hw : 0 < w) (hb : 0 < b) (path : prob_14_1_ColorPath) :
    0 ≤ prob_14_1_polyaPathProbability w b path := by
  simpa [prob_14_1_polyaPathProbability] using
    prob_14_1_polyaPathMassFrom_nonneg hw hb 0 0 path

/-- Recursive finite support for all Bool paths of a fixed length.  This
definition is tailored to induction on the first draw. -/
def prob_14_1_recursiveBoolPathsOfLength : ℕ → Finset prob_14_1_ColorPath
  | 0 => {[]}
  | n + 1 =>
      (prob_14_1_recursiveBoolPathsOfLength n).image (fun path => true :: path) ∪
        (prob_14_1_recursiveBoolPathsOfLength n).image (fun path => false :: path)

/-- The recursive finite path law has total mass one from every positive urn
state. -/
theorem prob_14_1_sum_polyaPathMassFrom_recursiveBoolPathsOfLength
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (white black i : ℕ) :
    (prob_14_1_recursiveBoolPathsOfLength i).sum
        (fun path => prob_14_1_polyaPathMassFrom w b white black path) = 1 := by
  induction i generalizing white black with
  | zero =>
      simp [prob_14_1_recursiveBoolPathsOfLength, prob_14_1_polyaPathMassFrom]
  | succ i ih =>
      let leftPaths :=
        (prob_14_1_recursiveBoolPathsOfLength i).image (fun path => true :: path)
      let rightPaths :=
        (prob_14_1_recursiveBoolPathsOfLength i).image (fun path => false :: path)
      have hdisj : Disjoint leftPaths rightPaths := by
        rw [Finset.disjoint_left]
        intro path hleft hright
        rcases Finset.mem_image.mp hleft with ⟨p, _hp, rfl⟩
        rcases Finset.mem_image.mp hright with ⟨q, _hq, hq⟩
        cases hq
      have hleft_sum :
          leftPaths.sum
              (fun path => prob_14_1_polyaPathMassFrom w b white black path) =
            prob_14_1_polyaPathStepProbabilityFrom w b white black true *
              (prob_14_1_recursiveBoolPathsOfLength i).sum
                (fun path => prob_14_1_polyaPathMassFrom w b (white + 1) black path) := by
        dsimp [leftPaths]
        rw [Finset.sum_image]
        · simp [prob_14_1_polyaPathMassFrom, Finset.mul_sum]
        · intro p _hp q _hq hpq
          simpa using hpq
      have hright_sum :
          rightPaths.sum
              (fun path => prob_14_1_polyaPathMassFrom w b white black path) =
            prob_14_1_polyaPathStepProbabilityFrom w b white black false *
              (prob_14_1_recursiveBoolPathsOfLength i).sum
                (fun path => prob_14_1_polyaPathMassFrom w b white (black + 1) path) := by
        dsimp [rightPaths]
        rw [Finset.sum_image]
        · simp [prob_14_1_polyaPathMassFrom, Finset.mul_sum]
        · intro p _hp q _hq hpq
          simpa using hpq
      rw [prob_14_1_recursiveBoolPathsOfLength]
      change (leftPaths ∪ rightPaths).sum
          (fun path => prob_14_1_polyaPathMassFrom w b white black path) = 1
      rw [Finset.sum_union hdisj, hleft_sum, hright_sum,
        ih (white + 1) black, ih white (black + 1)]
      have hden :
          b + w + ((white + black : ℕ) : ℝ) ≠ 0 := by
        have hcount : 0 ≤ ((white + black : ℕ) : ℝ) := by
          exact_mod_cast Nat.zero_le (white + black)
        nlinarith
      simp only [mul_one]
      change
        (w + (white : ℝ)) / (b + w + ((white + black : ℕ) : ℝ)) +
          (b + (black : ℝ)) / (b + w + ((white + black : ℕ) : ℝ)) = 1
      field_simp [hden]
      norm_num [Nat.cast_add]
      ring

/-- The recursive Bool-path support contains exactly the paths of the requested
length. -/
theorem prob_14_1_mem_recursiveBoolPathsOfLength_iff {i : ℕ}
    {path : prob_14_1_ColorPath} :
    path ∈ prob_14_1_recursiveBoolPathsOfLength i ↔ path.length = i := by
  induction i generalizing path with
  | zero =>
      cases path <;> simp [prob_14_1_recursiveBoolPathsOfLength]
  | succ i ih =>
      cases path with
      | nil =>
          simp [prob_14_1_recursiveBoolPathsOfLength]
      | cons color rest =>
          cases color <;> simp [prob_14_1_recursiveBoolPathsOfLength, ih]

/-- Two finite paths with the same length and white-count have the same Polya
path probability. -/
theorem prob_14_1_polyaPathProbability_eq_of_length_whiteDrawCount
    (w b : ℝ) {p q : prob_14_1_ColorPath}
    (hlen : p.length = q.length)
    (hwhite :
      prob_14_1_whiteDrawCount p = prob_14_1_whiteDrawCount q) :
    prob_14_1_polyaPathProbability w b p =
      prob_14_1_polyaPathProbability w b q := by
  have hp := prob_14_1_white_black_count_add_length p
  have hq := prob_14_1_white_black_count_add_length q
  have hblack :
      prob_14_1_blackDrawCount p = prob_14_1_blackDrawCount q := by
    omega
  rw [prob_14_1_polyaPathProbability_eq_count_formula,
    prob_14_1_polyaPathProbability_eq_count_formula, hlen, hwhite, hblack]

/-- Black count is determined by path length and white count. -/
theorem prob_14_1_blackDrawCount_eq_length_sub_whiteDrawCount
    (path : prob_14_1_ColorPath) :
    prob_14_1_blackDrawCount path =
      path.length - prob_14_1_whiteDrawCount path := by
  have h := prob_14_1_white_black_count_add_length path
  omega

/-- A fixed path of length `i` with `k` white draws has the common one-path
Polya mass used in the beta-binomial summation. -/
theorem prob_14_1_polyaPathProbability_eq_whiteCountPathMass
    (w b : ℝ) (path : prob_14_1_ColorPath) {i k : ℕ}
    (h_length : path.length = i)
    (h_white : prob_14_1_whiteDrawCount path = k) :
    prob_14_1_polyaPathProbability w b path =
      prob_14_1_risingFactorial w k *
        prob_14_1_risingFactorial b (i - k) /
      prob_14_1_risingFactorial (b + w) i := by
  have h_black :
      prob_14_1_blackDrawCount path = i - k := by
    rw [prob_14_1_blackDrawCount_eq_length_sub_whiteDrawCount, h_length, h_white]
  rw [prob_14_1_polyaPathProbability_eq_count_formula]
  simp [h_length, h_white, h_black]

/-- Boolean-function representation of a length-`i` color path. -/
abbrev prob_14_1_FinColorPath (i : ℕ) := Fin i → Bool

@[simp]
theorem prob_14_1_whiteDrawCount_ofFn {i : ℕ}
    (path : prob_14_1_FinColorPath i) :
    prob_14_1_whiteDrawCount (List.ofFn path) =
      prob_14_1_finWhiteCount path := by
  induction i with
  | zero =>
      simp [prob_14_1_finWhiteCount, prob_14_1_finWhiteSet,
        prob_14_1_whiteDrawCount]
  | succ i ih =>
      rw [List.ofFn_succ]
      cases h : path 0
      · have htail :
            prob_14_1_whiteDrawCount (List.ofFn fun j : Fin i => path j.succ) =
              prob_14_1_finWhiteCount (fun j : Fin i => path j.succ) := ih _
        simp [prob_14_1_whiteDrawCount, prob_14_1_finWhiteCount,
          prob_14_1_finWhiteSet, Fin.card_filter_univ_succ', h, htail]
      · have htail :
            prob_14_1_whiteDrawCount (List.ofFn fun j : Fin i => path j.succ) =
              prob_14_1_finWhiteCount (fun j : Fin i => path j.succ) := ih _
        simp [prob_14_1_whiteDrawCount, prob_14_1_finWhiteCount,
          prob_14_1_finWhiteSet, Fin.card_filter_univ_succ', h, htail]
        omega

@[simp]
theorem prob_14_1_length_ofFn {i : ℕ}
    (path : prob_14_1_FinColorPath i) :
    (List.ofFn path).length = i := by
  simp

/-- List-level image of all `Fin i → Bool` paths. -/
def prob_14_1_allBoolPathsOfLength (i : ℕ) : Finset prob_14_1_ColorPath :=
  (Finset.univ : Finset (prob_14_1_FinColorPath i)).image List.ofFn

/-- Every path in the explicit list-level support has length `i`. -/
theorem prob_14_1_mem_allBoolPathsOfLength_length {i : ℕ}
    {path : prob_14_1_ColorPath}
    (hpath : path ∈ prob_14_1_allBoolPathsOfLength i) :
    path.length = i := by
  classical
  rcases Finset.mem_image.mp hpath with ⟨f, _hf, rfl⟩
  simp

/-- The explicit list-level support contains exactly all length-`i` Bool paths. -/
theorem prob_14_1_mem_allBoolPathsOfLength_iff {i : ℕ}
    {path : prob_14_1_ColorPath} :
    path ∈ prob_14_1_allBoolPathsOfLength i ↔ path.length = i := by
  classical
  constructor
  · exact prob_14_1_mem_allBoolPathsOfLength_length
  · intro hlen
    refine Finset.mem_image.mpr ?_
    refine ⟨fun j : Fin i => path.get ⟨j.1, by simpa [hlen] using j.2⟩,
      Finset.mem_univ _, ?_⟩
    apply List.ext_get
    · simp [hlen]
    · intro n h_left h_right
      simp

/-- The recursive first-draw support and the function-image support are the
same finite set of length-`i` Bool paths. -/
theorem prob_14_1_recursiveBoolPathsOfLength_eq_allBoolPathsOfLength
    (i : ℕ) :
    prob_14_1_recursiveBoolPathsOfLength i =
      prob_14_1_allBoolPathsOfLength i := by
  ext path
  rw [prob_14_1_mem_recursiveBoolPathsOfLength_iff,
    prob_14_1_mem_allBoolPathsOfLength_iff]

/-- The concrete finite Polya path law on length-`i` color paths.  Its support
is the finite set of length-`i` paths, and its weights are the recursive urn
path probabilities. -/
noncomputable def prob_14_1_polyaPathPMF
    (w b : ℝ) (hw : 0 < w) (hb : 0 < b) (i : ℕ) :
    PMF prob_14_1_ColorPath :=
  PMF.ofFinset
    (fun path =>
      if path ∈ prob_14_1_allBoolPathsOfLength i then
        ENNReal.ofReal (prob_14_1_polyaPathProbability w b path)
      else
        0)
    (prob_14_1_allBoolPathsOfLength i)
    (by
      have hsum_real :
          (prob_14_1_allBoolPathsOfLength i).sum
              (fun path => prob_14_1_polyaPathProbability w b path) = 1 := by
        rw [← prob_14_1_recursiveBoolPathsOfLength_eq_allBoolPathsOfLength i]
        simpa [prob_14_1_polyaPathProbability] using
          prob_14_1_sum_polyaPathMassFrom_recursiveBoolPathsOfLength hw hb 0 0 i
      have hnonneg :
          ∀ path, path ∈ prob_14_1_allBoolPathsOfLength i →
            0 ≤ prob_14_1_polyaPathProbability w b path := by
        intro path _hpath
        exact prob_14_1_polyaPathProbability_nonneg hw hb path
      calc
        ∑ path ∈ prob_14_1_allBoolPathsOfLength i,
            (if path ∈ prob_14_1_allBoolPathsOfLength i then
              ENNReal.ofReal (prob_14_1_polyaPathProbability w b path)
            else 0)
            =
          ∑ path ∈ prob_14_1_allBoolPathsOfLength i,
            ENNReal.ofReal (prob_14_1_polyaPathProbability w b path) := by
              apply Finset.sum_congr rfl
              intro path hpath
              simp [hpath]
        _ = ENNReal.ofReal
              ((prob_14_1_allBoolPathsOfLength i).sum
                (fun path => prob_14_1_polyaPathProbability w b path)) := by
              rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
        _ = 1 := by
              rw [hsum_real]
              simp)
    (by
      intro path hpath
      simp [hpath])

@[simp]
theorem prob_14_1_polyaPathPMF_apply_mem
    (w b : ℝ) (hw : 0 < w) (hb : 0 < b) {i : ℕ}
    {path : prob_14_1_ColorPath}
    (hpath : path ∈ prob_14_1_allBoolPathsOfLength i) :
    prob_14_1_polyaPathPMF w b hw hb i path =
      ENNReal.ofReal (prob_14_1_polyaPathProbability w b path) := by
  simp [prob_14_1_polyaPathPMF, hpath]

@[simp]
theorem prob_14_1_polyaPathPMF_apply_notMem
    (w b : ℝ) (hw : 0 < w) (hb : 0 < b) {i : ℕ}
    {path : prob_14_1_ColorPath}
    (hpath : path ∉ prob_14_1_allBoolPathsOfLength i) :
    prob_14_1_polyaPathPMF w b hw hb i path = 0 := by
  simp [prob_14_1_polyaPathPMF, hpath]

/-- There are `choose i k` list paths of length `i` with `k` white draws. -/
theorem prob_14_1_allBoolPathsOfLength_card_whiteDrawCount_eq_choose
    (i k : ℕ) :
    ((prob_14_1_allBoolPathsOfLength i).filter
        (fun path => prob_14_1_whiteDrawCount path = k)).card = Nat.choose i k := by
  classical
  have hinj :
      Function.Injective (List.ofFn : prob_14_1_FinColorPath i → prob_14_1_ColorPath) :=
    List.ofFn_injective
  rw [prob_14_1_allBoolPathsOfLength, Finset.filter_image]
  · have hmap :
        ((Finset.univ : Finset (prob_14_1_FinColorPath i)).filter
            (fun path => prob_14_1_whiteDrawCount (List.ofFn path) = k)).card =
          ((Finset.univ : Finset (prob_14_1_FinColorPath i)).filter
            (fun path => prob_14_1_finWhiteCount path = k)).card := by
        congr 1
        ext path
        simp
    rw [Finset.card_image_of_injective _ hinj]
    rw [hmap]
    exact prob_14_1_card_filter_fin_paths_white_count i k

/-- If a finite path support has exactly `choose i k` paths with `k` white
draws, summing the path probabilities over that layer gives the mass formula. -/
theorem prob_14_1_polyaWhiteCountMass_sum_of_card
    (w b : ℝ) (paths : Finset prob_14_1_ColorPath) {i k : ℕ}
    (h_length : ∀ path ∈ paths, path.length = i)
    (h_card :
      (paths.filter (fun path => prob_14_1_whiteDrawCount path = k)).card =
        Nat.choose i k) :
    (paths.filter (fun path => prob_14_1_whiteDrawCount path = k)).sum
        (fun path => prob_14_1_polyaPathProbability w b path) =
      prob_14_1_polyaWhiteMassFormula w b i k := by
  classical
  let layer := paths.filter (fun path => prob_14_1_whiteDrawCount path = k)
  have h_each :
      ∀ path ∈ layer,
        prob_14_1_polyaPathProbability w b path =
          prob_14_1_risingFactorial w k *
            prob_14_1_risingFactorial b (i - k) /
          prob_14_1_risingFactorial (b + w) i := by
    intro path hpath
    have h_mem_paths : path ∈ paths := by
      simpa [layer] using (Finset.mem_of_mem_filter path hpath)
    have h_white : prob_14_1_whiteDrawCount path = k := by
      simpa [layer] using (Finset.mem_filter.mp hpath).2
    exact prob_14_1_polyaPathProbability_eq_whiteCountPathMass
      w b path (h_length path h_mem_paths) h_white
  calc
    (paths.filter (fun path => prob_14_1_whiteDrawCount path = k)).sum
        (fun path => prob_14_1_polyaPathProbability w b path)
        = layer.sum (fun path => prob_14_1_polyaPathProbability w b path) := by
            rfl
    _ = layer.sum (fun _ =>
          (prob_14_1_risingFactorial w k *
            prob_14_1_risingFactorial b (i - k) /
          prob_14_1_risingFactorial (b + w) i)) := by
            apply Finset.sum_congr rfl
            intro path hpath
            exact h_each path hpath
    _ = layer.card *
          (prob_14_1_risingFactorial w k *
            prob_14_1_risingFactorial b (i - k) /
          prob_14_1_risingFactorial (b + w) i) := by
            simp
    _ = prob_14_1_polyaWhiteMassFormula w b i k := by
            simp [layer, h_card, prob_14_1_polyaWhiteMassFormula]
            ring

/-- Summing fixed-path masses over all length-`i` paths with `k` white draws
produces the beta-binomial mass formula. -/
theorem prob_14_1_polyaWhiteCountMass_sum_allBoolPathsOfLength
    (w b : ℝ) (i k : ℕ) :
    ((prob_14_1_allBoolPathsOfLength i).filter
        (fun path => prob_14_1_whiteDrawCount path = k)).sum
        (fun path => prob_14_1_polyaPathProbability w b path) =
      prob_14_1_polyaWhiteMassFormula w b i k := by
  exact prob_14_1_polyaWhiteCountMass_sum_of_card w b
    (prob_14_1_allBoolPathsOfLength i)
    (fun path hpath => prob_14_1_mem_allBoolPathsOfLength_length hpath)
    (prob_14_1_allBoolPathsOfLength_card_whiteDrawCount_eq_choose i k)

/-- Fin-function version of the beta-binomial layer sum. -/
theorem prob_14_1_polyaWhiteCountMass_sum_fin_paths
    (w b : ℝ) (i k : ℕ) :
    ((Finset.univ : Finset (prob_14_1_FinColorPath i)).filter
        (fun path => prob_14_1_finWhiteCount path = k)).sum
        (fun path => prob_14_1_polyaPathProbability w b (List.ofFn path)) =
      prob_14_1_polyaWhiteMassFormula w b i k := by
  classical
  let finLayer :=
    (Finset.univ : Finset (prob_14_1_FinColorPath i)).filter
      (fun path => prob_14_1_finWhiteCount path = k)
  have h_image :
      finLayer.image (List.ofFn : prob_14_1_FinColorPath i → prob_14_1_ColorPath) =
        (prob_14_1_allBoolPathsOfLength i).filter
          (fun path => prob_14_1_whiteDrawCount path = k) := by
    ext path
    constructor
    · intro hpath
      rcases Finset.mem_image.mp hpath with ⟨f, hf, rfl⟩
      have hwhite : prob_14_1_finWhiteCount f = k := by
        simpa [finLayer] using (Finset.mem_filter.mp hf).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩,
          by simpa using hwhite⟩
    · intro hpath
      rcases Finset.mem_filter.mp hpath with ⟨hmem, hwhite⟩
      rcases Finset.mem_image.mp hmem with ⟨f, _hf, rfl⟩
      refine Finset.mem_image.mpr ⟨f, ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by simpa using hwhite⟩
  have hsum_image :
      (finLayer.image (List.ofFn : prob_14_1_FinColorPath i → prob_14_1_ColorPath)).sum
          (fun path => prob_14_1_polyaPathProbability w b path) =
        finLayer.sum
          (fun path => prob_14_1_polyaPathProbability w b (List.ofFn path)) := by
    rw [Finset.sum_image]
    intro p _hp q _hq hpq
    exact List.ofFn_injective hpq
  calc
    ((Finset.univ : Finset (prob_14_1_FinColorPath i)).filter
        (fun path => prob_14_1_finWhiteCount path = k)).sum
        (fun path => prob_14_1_polyaPathProbability w b (List.ofFn path))
        = finLayer.sum
            (fun path => prob_14_1_polyaPathProbability w b (List.ofFn path)) := by
            rfl
    _ = (finLayer.image (List.ofFn : prob_14_1_FinColorPath i → prob_14_1_ColorPath)).sum
          (fun path => prob_14_1_polyaPathProbability w b path) := by
            exact hsum_image.symm
    _ = ((prob_14_1_allBoolPathsOfLength i).filter
          (fun path => prob_14_1_whiteDrawCount path = k)).sum
          (fun path => prob_14_1_polyaPathProbability w b path) := by
            rw [h_image]
    _ = prob_14_1_polyaWhiteMassFormula w b i k := by
            exact prob_14_1_polyaWhiteCountMass_sum_allBoolPathsOfLength w b i k

/-- The explicit beta-binomial masses obtained from the finite Polya path law
sum to one on the finite support `{0, ..., i}`. -/
theorem prob_14_1_polyaWhiteMassFormula_sum_range_eq_one
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) (i : ℕ) :
    (Finset.range (i + 1)).sum
      (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b i k) = 1 := by
  classical
  let f : prob_14_1_FinColorPath i → ℝ :=
    fun path => prob_14_1_polyaPathProbability w b (List.ofFn path)
  have hsum_list :
      (prob_14_1_allBoolPathsOfLength i).sum
          (fun path => prob_14_1_polyaPathProbability w b path) = 1 := by
    rw [← prob_14_1_recursiveBoolPathsOfLength_eq_allBoolPathsOfLength i]
    simpa [prob_14_1_polyaPathProbability] using
      prob_14_1_sum_polyaPathMassFrom_recursiveBoolPathsOfLength hw hb 0 0 i
  have hsum_fin :
      ∑ path : prob_14_1_FinColorPath i, f path = 1 := by
    rw [← hsum_list]
    rw [prob_14_1_allBoolPathsOfLength, Finset.sum_image]
    intro p _hp q _hq hpq
    exact List.ofFn_injective hpq
  calc
    (Finset.range (i + 1)).sum
        (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b i k)
        =
      (Finset.range (i + 1)).sum
        (fun k : ℕ =>
          ((Finset.univ : Finset (prob_14_1_FinColorPath i)).filter
            (fun path => prob_14_1_finWhiteCount path = k)).sum f) := by
          apply Finset.sum_congr rfl
          intro k _hk
          exact (prob_14_1_polyaWhiteCountMass_sum_fin_paths w b i k).symm
    _ = ∑ path : prob_14_1_FinColorPath i, f path := by
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro path _hpath
          have hcount_le : prob_14_1_finWhiteCount path ≤ i := by
            rw [prob_14_1_finWhiteCount, prob_14_1_finWhiteSet]
            simpa [Fintype.card_fin] using
              (Finset.card_le_univ (prob_14_1_finWhiteSet path))
          have hcount_mem :
              prob_14_1_finWhiteCount path ∈ Finset.range (i + 1) :=
            Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hcount_le)
          calc
            (∑ x ∈ Finset.range (i + 1),
              if prob_14_1_finWhiteCount path = x then f path else 0)
                = (if prob_14_1_finWhiteCount path ∈ Finset.range (i + 1) then
                    f path else 0) := by
                    simpa [eq_comm] using
                      (Finset.sum_ite_eq'
                        (Finset.range (i + 1))
                        (prob_14_1_finWhiteCount path)
                        (fun _ : ℕ => f path))
            _ = f path := by simp [hcount_mem]
    _ = 1 := hsum_fin

/-- ENNReal normalization of finite Polya path probabilities on `Fin i → Bool`. -/
theorem prob_14_1_polyaPathProbability_ennreal_sum_fin_paths_eq_one
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) (i : ℕ) :
    ∑ path : prob_14_1_FinColorPath i,
      ENNReal.ofReal
        (prob_14_1_polyaPathProbability w b (List.ofFn path)) = 1 := by
  classical
  have hsum_list :
      (prob_14_1_allBoolPathsOfLength i).sum
          (fun path => prob_14_1_polyaPathProbability w b path) = 1 := by
    rw [← prob_14_1_recursiveBoolPathsOfLength_eq_allBoolPathsOfLength i]
    simpa [prob_14_1_polyaPathProbability] using
      prob_14_1_sum_polyaPathMassFrom_recursiveBoolPathsOfLength hw hb 0 0 i
  have hsum_real :
      ∑ path : prob_14_1_FinColorPath i,
        prob_14_1_polyaPathProbability w b (List.ofFn path) = 1 := by
    rw [← hsum_list]
    rw [prob_14_1_allBoolPathsOfLength, Finset.sum_image]
    intro p _hp q _hq hpq
    exact List.ofFn_injective hpq
  have hnonneg :
      ∀ path, path ∈ (Finset.univ : Finset (prob_14_1_FinColorPath i)) →
        0 ≤ prob_14_1_polyaPathProbability w b (List.ofFn path) := by
    intro path _hpath
    exact prob_14_1_polyaPathProbability_nonneg hw hb (List.ofFn path)
  rw [← ENNReal.ofReal_sum_of_nonneg hnonneg, hsum_real]
  simp

/-- Finite Polya path PMF on the function representation of length-`i` paths. -/
noncomputable def prob_14_1_polyaFinPathPMF
    (w b : ℝ) (hw : 0 < w) (hb : 0 < b) (i : ℕ) :
    PMF (prob_14_1_FinColorPath i) :=
  PMF.ofFintype
    (fun path =>
      ENNReal.ofReal
        (prob_14_1_polyaPathProbability w b (List.ofFn path)))
    (prob_14_1_polyaPathProbability_ennreal_sum_fin_paths_eq_one hw hb i)

/-- The source-owned white-count law generated by the finite Polya path law. -/
noncomputable def prob_14_1_polyaWhiteCountLaw
    (w b : ℝ) (hw : 0 < w) (hb : 0 < b) (i : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨((prob_14_1_polyaFinPathPMF w b hw hb i).map
      (fun path : prob_14_1_FinColorPath i =>
        (prob_14_1_finWhiteCount path : ℝ))).toMeasure,
    PMF.toMeasure.isProbabilityMeasure _⟩

/-- The internally constructed Polya white-count law has the beta-binomial
atom formula. -/
theorem prob_14_1_polyaWhiteCountLaw_atom
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) {i k : ℕ} :
    (prob_14_1_polyaWhiteCountLaw w b hw hb i : Measure ℝ)
      {x : ℝ | x = (k : ℝ)} =
    ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula w b i k) := by
  classical
  change
    (((prob_14_1_polyaFinPathPMF w b hw hb i).map
      (fun path : prob_14_1_FinColorPath i =>
        (prob_14_1_finWhiteCount path : ℝ))).toMeasure)
      {x : ℝ | x = (k : ℝ)} =
    ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula w b i k)
  rw [show {x : ℝ | x = (k : ℝ)} = ({(k : ℝ)} : Set ℝ) by
    ext x
    simp]
  rw [PMF.toMeasure_apply_singleton
    ((prob_14_1_polyaFinPathPMF w b hw hb i).map
      (fun path : prob_14_1_FinColorPath i =>
        (prob_14_1_finWhiteCount path : ℝ)))
    (k : ℝ) (measurableSet_singleton (k : ℝ))]
  rw [PMF.map_apply, tsum_fintype]
  have hsum_filter :
      (∑ path : prob_14_1_FinColorPath i,
        if ((k : ℝ) = (prob_14_1_finWhiteCount path : ℝ)) then
          prob_14_1_polyaFinPathPMF w b hw hb i path
        else 0) =
      ((Finset.univ : Finset (prob_14_1_FinColorPath i)).filter
        (fun path => prob_14_1_finWhiteCount path = k)).sum
        (fun path =>
          ENNReal.ofReal
            (prob_14_1_polyaPathProbability w b (List.ofFn path))) := by
    rw [← Finset.sum_filter]
    have hfilter_cast :
        ((Finset.univ : Finset (prob_14_1_FinColorPath i)).filter
          (fun path => (k : ℝ) = (prob_14_1_finWhiteCount path : ℝ))) =
        ((Finset.univ : Finset (prob_14_1_FinColorPath i)).filter
          (fun path => prob_14_1_finWhiteCount path = k)) := by
      ext path
      simp [eq_comm]
    rw [hfilter_cast]
    apply Finset.sum_congr rfl
    intro path _hpath
    simp [prob_14_1_polyaFinPathPMF]
  rw [hsum_filter]
  have hnonneg :
      ∀ path, path ∈
          ((Finset.univ : Finset (prob_14_1_FinColorPath i)).filter
            (fun path => prob_14_1_finWhiteCount path = k)) →
        0 ≤ prob_14_1_polyaPathProbability w b (List.ofFn path) := by
    intro path _hpath
    exact prob_14_1_polyaPathProbability_nonneg hw hb (List.ofFn path)
  rw [← ENNReal.ofReal_sum_of_nonneg hnonneg]
  rw [prob_14_1_polyaWhiteCountMass_sum_fin_paths]

namespace prob_14_1_PolyaUrnBetaSetup

/-- The white-count laws are derived from the finite Polya path law. -/
noncomputable def whiteCountLaws (S : prob_14_1_PolyaUrnBetaSetup) :
    ℕ → ProbabilityMeasure ℝ :=
  fun i => prob_14_1_polyaWhiteCountLaw S.w S.b S.w_pos S.b_pos i

end prob_14_1_PolyaUrnBetaSetup

/-- Source obligation for Problem 14.1(a): derive the beta-binomial
white-count mass formula from the finite Polya urn path-counting model. -/
def prob_14_1_finitePolyaWhiteCountMass
    (S : prob_14_1_PolyaUrnBetaSetup) : Prop :=
  ∀ i k : ℕ, 1 ≤ i → k ≤ i →
    (S.whiteCountLaws i : Measure ℝ) {x : ℝ | x = (k : ℝ)} =
      ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula S.w S.b i k)

/-- Source obligation for Problem 14.1(b): derive the scaled-law CDF limit
from the beta-binomial local asymptotics and the Beta Riemann-sum argument. -/
def prob_14_1_stirlingBetaCdfConvergence
    (S : prob_14_1_PolyaUrnBetaSetup) : Prop :=
  prob_14_1_cdfConvergence
    (prob_14_1_whiteFractionLaws S.whiteCountLaws) S.beta.law

/-- Part (a), parent-owned: the internally constructed count law has the
beta-binomial atom formula. -/
theorem prob_14_1_finite_polya_white_count_mass
    (S : prob_14_1_PolyaUrnBetaSetup) :
    prob_14_1_finitePolyaWhiteCountMass S := by
  intro i k _hi _hk
  exact prob_14_1_polyaWhiteCountLaw_atom S.w_pos S.b_pos

/-- Part (a): the probability mass formula for the number of white balls drawn
in the first `i` steps. -/
theorem prob_14_1_white_count_mass
    (S : prob_14_1_PolyaUrnBetaSetup) {i k : ℕ}
    (hi : 1 ≤ i) (hk : k ≤ i) :
    (S.whiteCountLaws i : Measure ℝ) {x : ℝ | x = (k : ℝ)} =
      ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula S.w S.b i k) :=
  prob_14_1_finite_polya_white_count_mass S i k hi hk

/-- The scaled law has the corresponding atom at `k / i`. -/
theorem prob_14_1_white_fraction_mass
    (S : prob_14_1_PolyaUrnBetaSetup) {i k : ℕ}
    (hi : 1 ≤ i) (hk : k ≤ i) :
    (prob_14_1_whiteFractionLaws S.whiteCountLaws i : Measure ℝ)
        {x : ℝ | x = (k : ℝ) / (i : ℝ)} =
      ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula S.w S.b i k) := by
  rw [prob_14_1_whiteFractionLaws]
  rw [prob_14_1_scaled_count_law_atom (S.whiteCountLaws i) hi]
  exact prob_14_1_white_count_mass S hi hk

/-- If the count-law atom is represented by the concrete finite-path sum, then
the displayed beta-binomial atom formula follows.  The source-closing work is
to construct that count law internally, not to assume the final formula. -/
theorem prob_14_1_measure_atom_eq_ofReal_polyaWhiteMassFormula_of_path_sum
    (S : prob_14_1_PolyaUrnBetaSetup) {i k : ℕ}
    (h_atom_sum :
      (S.whiteCountLaws i : Measure ℝ) {x : ℝ | x = (k : ℝ)} =
        ENNReal.ofReal (((prob_14_1_allBoolPathsOfLength i).filter
          (fun path => prob_14_1_whiteDrawCount path = k)).sum
            (fun path => prob_14_1_polyaPathProbability S.w S.b path))) :
    (S.whiteCountLaws i : Measure ℝ) {x : ℝ | x = (k : ℝ)} =
      ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula S.w S.b i k) := by
  rw [h_atom_sum]
  congr 1
  exact prob_14_1_polyaWhiteCountMass_sum_allBoolPathsOfLength S.w S.b i k

