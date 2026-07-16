import Mathlib
import ToyApollo.Output.def_4_3_sup_inf

/-!
Definition 4.4: limsup and liminf.

The original complete-lattice constructions remain the reusable support layer. For a real
sequence, total values live in EReal; finite real values are exposed separately through
Filter.limsup and Filter.liminf with the necessary boundedness hypotheses.
-/

/-! ## Complete-lattice support layer -/

/-- Tail supremum of a sequence starting at index n. -/
noncomputable def tailSup {α : Type*} [CompleteLattice α] (a : ℕ → α) (n : ℕ) : α :=
  ⨆ k : ℕ, a (n + k)

/-- Tail infimum of a sequence starting at index n. -/
noncomputable def tailInf {α : Type*} [CompleteLattice α] (a : ℕ → α) (n : ℕ) : α :=
  ⨅ k : ℕ, a (n + k)

/-- Limsup of a sequence in a complete lattice. -/
noncomputable def seqLimsup {α : Type*} [CompleteLattice α] (a : ℕ → α) : α :=
  ⨅ n : ℕ, tailSup a n

/-- Liminf of a sequence in a complete lattice. -/
noncomputable def seqLiminf {α : Type*} [CompleteLattice α] (a : ℕ → α) : α :=
  ⨆ n : ℕ, tailInf a n

/-- Rewrite the addition-indexed tail with the shifted index on the left. -/
theorem tailSup_eq_iSup_add_left
    {α : Type*} [CompleteLattice α] (a : ℕ → α) (n : ℕ) :
    tailSup a n = ⨆ i : ℕ, a (i + n) := by
  simp [tailSup, Nat.add_comm]

/-- Dual addition-indexed tail rewrite. -/
theorem tailInf_eq_iInf_add_left
    {α : Type*} [CompleteLattice α] (a : ℕ → α) (n : ℕ) :
    tailInf a n = ⨅ i : ℕ, a (i + n) := by
  simp [tailInf, Nat.add_comm]

/-- The addition-indexed tail supremum is the supremum over the order-bounded tail. -/
theorem tailSup_eq_iSup_ge
    {α : Type*} [CompleteLattice α] (a : ℕ → α) (n : ℕ) :
    tailSup a n = ⨆ i : ℕ, ⨆ (_hni : n ≤ i), a i := by
  calc
    tailSup a n = ⨆ i : ℕ, a (i + n) := tailSup_eq_iSup_add_left a n
    _ = ⨆ i : ℕ, ⨆ (_hni : n ≤ i), a i :=
      (iSup_ge_eq_iSup_nat_add a n).symm

/-- The addition-indexed tail infimum is the infimum over the order-bounded tail. -/
theorem tailInf_eq_iInf_ge
    {α : Type*} [CompleteLattice α] (a : ℕ → α) (n : ℕ) :
    tailInf a n = ⨅ i : ℕ, ⨅ (_hni : n ≤ i), a i := by
  calc
    tailInf a n = ⨅ i : ℕ, a (i + n) := tailInf_eq_iInf_add_left a n
    _ = ⨅ i : ℕ, ⨅ (_hni : n ≤ i), a i :=
      (iInf_ge_eq_iInf_nat_add a n).symm

/-- The support-layer limsup agrees with Mathlib's filter limsup. -/
theorem seqLimsup_eq_filter_limsup
    {α : Type*} [CompleteLattice α] (a : ℕ → α) :
    seqLimsup a = Filter.limsup a Filter.atTop := by
  simpa [seqLimsup, tailSup, Nat.add_comm] using
    (Filter.limsup_eq_iInf_iSup_of_nat' (u := a)).symm

/-- The support-layer liminf agrees with Mathlib's filter liminf. -/
theorem seqLiminf_eq_filter_liminf
    {α : Type*} [CompleteLattice α] (a : ℕ → α) :
    seqLiminf a = Filter.liminf a Filter.atTop := by
  simpa [seqLiminf, tailInf, Nat.add_comm] using
    (Filter.liminf_eq_iSup_iInf_of_nat' (u := a)).symm

/-! ## Total extended-real interface -/

/-- Total limsup of a real sequence, allowing bottom and top. -/
noncomputable def realSeqLimsupEReal (a : ℕ → ℝ) : EReal :=
  seqLimsup (fun n => (a n : EReal))

/-- Total liminf of a real sequence, allowing bottom and top. -/
noncomputable def realSeqLiminfEReal (a : ℕ → ℝ) : EReal :=
  seqLiminf (fun n => (a n : EReal))

/-- Filter bridge for the total extended-real limsup. -/
theorem realSeqLimsupEReal_eq_filter (a : ℕ → ℝ) :
    realSeqLimsupEReal a =
      Filter.limsup (fun n => (a n : EReal)) Filter.atTop := by
  simpa [realSeqLimsupEReal] using
    seqLimsup_eq_filter_limsup (fun n => (a n : EReal))

/-- Filter bridge for the total extended-real liminf. -/
theorem realSeqLiminfEReal_eq_filter (a : ℕ → ℝ) :
    realSeqLiminfEReal a =
      Filter.liminf (fun n => (a n : EReal)) Filter.atTop := by
  simpa [realSeqLiminfEReal] using
    seqLiminf_eq_filter_liminf (fun n => (a n : EReal))

/-- Total extended-real liminf never exceeds total extended-real limsup. -/
theorem realSeqLiminfEReal_le_realSeqLimsupEReal (a : ℕ → ℝ) :
    realSeqLiminfEReal a ≤ realSeqLimsupEReal a := by
  rw [realSeqLiminfEReal_eq_filter, realSeqLimsupEReal_eq_filter]
  exact Filter.liminf_le_limsup

/-! ## Finite real interface and textbook epsilon characterizations -/

/-- The finite-real limsup adapter. -/
noncomputable def realSeqLimsup (a : ℕ → ℝ) : ℝ :=
  Filter.limsup a Filter.atTop

/-- The finite-real liminf adapter. -/
noncomputable def realSeqLiminf (a : ℕ → ℝ) : ℝ :=
  Filter.liminf a Filter.atTop

/-- Eventually the sequence lies strictly below r + epsilon. -/
def EventuallyLtAddEpsilon (a : ℕ → ℝ) (r : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k → a k < r + ε

/-- Eventually the sequence lies strictly above s - epsilon. -/
def EventuallySubEpsilonLt (a : ℕ → ℝ) (s : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k → s - ε < a k

/-- The finite limsup is the least real with the eventual upper-epsilon property. -/
theorem realSeqLimsup_isLeast_eventuallyLtAddEpsilon
    (a : ℕ → ℝ)
    (hCobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop a)
    (hBdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop a) :
    IsLeast {r : ℝ | EventuallyLtAddEpsilon a r} (realSeqLimsup a) := by
  change IsLeast {r : ℝ | EventuallyLtAddEpsilon a r}
    (Filter.limsup a Filter.atTop)
  constructor
  · intro ε hε
    have hEventual :
        ∀ᶠ k in Filter.atTop, a k < Filter.limsup a Filter.atTop + ε :=
      ((Filter.limsup_le_iff hCobdd hBdd).1 le_rfl)
        (Filter.limsup a Filter.atTop + ε) (by linarith)
    exact Filter.eventually_atTop.1 hEventual
  · intro r hr
    apply (Filter.limsup_le_iff hCobdd hBdd).2
    intro y hry
    have hε : 0 < y - r := sub_pos.mpr hry
    obtain ⟨N, hN⟩ := hr (y - r) hε
    exact Filter.eventually_atTop.2
      ⟨N, fun k hk => by
        have hak := hN k hk
        linarith⟩

/-- The finite liminf is the greatest real with the eventual lower-epsilon property. -/
theorem realSeqLiminf_isGreatest_eventuallySubEpsilonLt
    (a : ℕ → ℝ)
    (hCobdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop a)
    (hBdd : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop a) :
    IsGreatest {s : ℝ | EventuallySubEpsilonLt a s} (realSeqLiminf a) := by
  change IsGreatest {s : ℝ | EventuallySubEpsilonLt a s}
    (Filter.liminf a Filter.atTop)
  constructor
  · intro ε hε
    have hEventual :
        ∀ᶠ k in Filter.atTop, Filter.liminf a Filter.atTop - ε < a k :=
      ((Filter.le_liminf_iff hCobdd hBdd).1 le_rfl)
        (Filter.liminf a Filter.atTop - ε) (by linarith)
    exact Filter.eventually_atTop.1 hEventual
  · intro s hs
    apply (Filter.le_liminf_iff hCobdd hBdd).2
    intro y hys
    have hε : 0 < s - y := sub_pos.mpr hys
    obtain ⟨N, hN⟩ := hs (s - y) hε
    exact Filter.eventually_atTop.2
      ⟨N, fun k hk => by
        have hak := hN k hk
        linarith⟩

/-- Under two-sided boundedness, finite liminf is at most finite limsup. -/
theorem realSeqLiminf_le_realSeqLimsup
    (a : ℕ → ℝ)
    (hAbove : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop a)
    (hBelow : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop a) :
    realSeqLiminf a ≤ realSeqLimsup a := by
  change Filter.liminf a Filter.atTop ≤ Filter.limsup a Filter.atTop
  exact Filter.liminf_le_limsup hAbove hBelow

/-- A convergent sequence has both finite adapters equal to its supplied limit. -/
theorem realSeqLimsup_liminf_eq_limit
    {a : ℕ → ℝ} {l : ℝ}
    (h : Filter.Tendsto a Filter.atTop (nhds l)) :
    realSeqLimsup a = l ∧ realSeqLiminf a = l := by
  exact ⟨h.limsup_eq, h.liminf_eq⟩

/-- Consequently, a convergent sequence has equal finite liminf and limsup. -/
theorem realSeqLiminf_eq_limsup_of_tendsto
    {a : ℕ → ℝ} {l : ℝ}
    (h : Filter.Tendsto a Filter.atTop (nhds l)) :
    realSeqLiminf a = realSeqLimsup a := by
  obtain ⟨hsup, hinf⟩ := realSeqLimsup_liminf_eq_limit h
  exact hinf.trans hsup.symm

/-! ## Cross-layer bridges -/

/-- Under finite limsup hypotheses, the total value is the coerced real value. -/
theorem realSeqLimsupEReal_eq_coe_realSeqLimsup
    (a : ℕ → ℝ)
    (hCobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop a)
    (hBdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop a) :
    realSeqLimsupEReal a = (realSeqLimsup a : EReal) := by
  have hMap :
      Real.toEReal (Filter.limsup a Filter.atTop) =
        Filter.limsup (Real.toEReal ∘ a) Filter.atTop :=
    Monotone.map_limsup_of_continuousAt
      (F := Filter.atTop) (R := ℝ) (S := EReal)
      EReal.coe_strictMono.monotone a
      continuous_coe_real_ereal.continuousAt hBdd hCobdd
  rw [realSeqLimsupEReal_eq_filter]
  change Filter.limsup (fun n => (a n : EReal)) Filter.atTop =
    Real.toEReal (Filter.limsup a Filter.atTop)
  simpa only [Function.comp_def] using hMap.symm

/-- Under finite liminf hypotheses, the total value is the coerced real value. -/
theorem realSeqLiminfEReal_eq_coe_realSeqLiminf
    (a : ℕ → ℝ)
    (hCobdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop a)
    (hBdd : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop a) :
    realSeqLiminfEReal a = (realSeqLiminf a : EReal) := by
  have hMap :
      Real.toEReal (Filter.liminf a Filter.atTop) =
        Filter.liminf (Real.toEReal ∘ a) Filter.atTop :=
    Monotone.map_liminf_of_continuousAt
      (F := Filter.atTop) (R := ℝ) (S := EReal)
      EReal.coe_strictMono.monotone a
      continuous_coe_real_ereal.continuousAt hCobdd hBdd
  rw [realSeqLiminfEReal_eq_filter]
  change Filter.liminf (fun n => (a n : EReal)) Filter.atTop =
    Real.toEReal (Filter.liminf a Filter.atTop)
  simpa only [Function.comp_def] using hMap.symm

/-- The total values of a convergent sequence equal the coerced limit. -/
theorem realSeqLimsupEReal_liminfEReal_eq_limit
    {a : ℕ → ℝ} {l : ℝ}
    (h : Filter.Tendsto a Filter.atTop (nhds l)) :
    realSeqLimsupEReal a = (l : EReal) ∧
      realSeqLiminfEReal a = (l : EReal) := by
  have hEReal :
      Filter.Tendsto (fun n => (a n : EReal)) Filter.atTop (nhds (l : EReal)) := by
    simpa only [Function.comp_def] using
      (continuous_coe_real_ereal.tendsto l).comp h
  constructor
  · rw [realSeqLimsupEReal_eq_filter]
    exact hEReal.limsup_eq
  · rw [realSeqLiminfEReal_eq_filter]
    exact hEReal.liminf_eq

/-! ## One-based source formulas -/

/-- Convert a positive-natural-indexed source sequence to zero-based Nat indexing. -/
def oneBasedToZeroBased {α : Type*} (a : PNat → α) : ℕ → α :=
  fun n => a n.succPNat

/-- Textbook one-based infimum-of-tail-suprema formula. -/
theorem realSeqLimsupEReal_oneBased_eq_iInf_iSup
    (a : PNat → ℝ) :
    realSeqLimsupEReal (oneBasedToZeroBased a) =
      ⨅ j : PNat, ⨆ k : PNat, ⨆ (_hjk : j ≤ k), (a k : EReal) := by
  rw [realSeqLimsupEReal_eq_filter, Filter.limsup_eq_iInf_iSup_of_nat]
  simp only [oneBasedToZeroBased]
  let e : PNat ≃ ℕ := OrderIso.pnatIsoNat.toEquiv
  calc
    (⨅ n : ℕ, ⨆ i : ℕ, ⨆ (_hni : n ≤ i), (a i.succPNat : EReal)) =
        ⨅ j : PNat, ⨆ i : ℕ, ⨆ (_hji : j.natPred ≤ i),
          (a i.succPNat : EReal) := by
      symm
      simpa [e, OrderIso.pnatIsoNat, Equiv.pnatEquivNat] using
        (e.iInf_comp
          (g := fun n : ℕ =>
            ⨆ i : ℕ, ⨆ (_hni : n ≤ i), (a i.succPNat : EReal)))
    _ = ⨅ j : PNat, ⨆ k : PNat, ⨆ (_hjk : j.natPred ≤ k.natPred),
          (a k.natPred.succPNat : EReal) := by
      apply iInf_congr
      intro j
      symm
      simpa [e, OrderIso.pnatIsoNat, Equiv.pnatEquivNat] using
        (e.iSup_comp
          (g := fun i : ℕ =>
            ⨆ (_hji : j.natPred ≤ i), (a i.succPNat : EReal)))
    _ = ⨅ j : PNat, ⨆ k : PNat, ⨆ (_hjk : j ≤ k), (a k : EReal) := by
      simp only [PNat.natPred_le_natPred, PNat.succPNat_natPred]

/-- Textbook one-based supremum-of-tail-infima formula. -/
theorem realSeqLiminfEReal_oneBased_eq_iSup_iInf
    (a : PNat → ℝ) :
    realSeqLiminfEReal (oneBasedToZeroBased a) =
      ⨆ j : PNat, ⨅ k : PNat, ⨅ (_hjk : j ≤ k), (a k : EReal) := by
  rw [realSeqLiminfEReal_eq_filter, Filter.liminf_eq_iSup_iInf_of_nat]
  simp only [oneBasedToZeroBased]
  let e : PNat ≃ ℕ := OrderIso.pnatIsoNat.toEquiv
  calc
    (⨆ n : ℕ, ⨅ i : ℕ, ⨅ (_hni : n ≤ i), (a i.succPNat : EReal)) =
        ⨆ j : PNat, ⨅ i : ℕ, ⨅ (_hji : j.natPred ≤ i),
          (a i.succPNat : EReal) := by
      symm
      simpa [e, OrderIso.pnatIsoNat, Equiv.pnatEquivNat] using
        (e.iSup_comp
          (g := fun n : ℕ =>
            ⨅ i : ℕ, ⨅ (_hni : n ≤ i), (a i.succPNat : EReal)))
    _ = ⨆ j : PNat, ⨅ k : PNat, ⨅ (_hjk : j.natPred ≤ k.natPred),
          (a k.natPred.succPNat : EReal) := by
      apply iSup_congr
      intro j
      symm
      simpa [e, OrderIso.pnatIsoNat, Equiv.pnatEquivNat] using
        (e.iInf_comp
          (g := fun i : ℕ =>
            ⨅ (_hji : j.natPred ≤ i), (a i.succPNat : EReal)))
    _ = ⨆ j : PNat, ⨅ k : PNat, ⨅ (_hjk : j ≤ k), (a k : EReal) := by
      simp only [PNat.natPred_le_natPred, PNat.succPNat_natPred]

/-! ## Finite-prefix and arbitrary-shift invariance -/

/-- Delete the first Nat-indexed term. -/
def dropFirst {α : Type*} (a : ℕ → α) : ℕ → α :=
  fun n => a (n + 1)

/-- Arbitrary finite shifts preserve the finite-real limsup. -/
theorem realSeqLimsup_nat_add (a : ℕ → ℝ) (m : ℕ) :
    realSeqLimsup (fun n => a (n + m)) = realSeqLimsup a := by
  simpa [realSeqLimsup] using Filter.limsup_nat_add a m

/-- Arbitrary finite shifts preserve the finite-real liminf. -/
theorem realSeqLiminf_nat_add (a : ℕ → ℝ) (m : ℕ) :
    realSeqLiminf (fun n => a (n + m)) = realSeqLiminf a := by
  simpa [realSeqLiminf] using Filter.liminf_nat_add a m

/-- Arbitrary finite shifts preserve the total extended-real limsup. -/
theorem realSeqLimsupEReal_nat_add (a : ℕ → ℝ) (m : ℕ) :
    realSeqLimsupEReal (fun n => a (n + m)) = realSeqLimsupEReal a := by
  change seqLimsup (fun n => (a (n + m) : EReal)) =
    seqLimsup (fun n => (a n : EReal))
  rw [seqLimsup_eq_filter_limsup, seqLimsup_eq_filter_limsup]
  exact Filter.limsup_nat_add (fun n => (a n : EReal)) m

/-- Arbitrary finite shifts preserve the total extended-real liminf. -/
theorem realSeqLiminfEReal_nat_add (a : ℕ → ℝ) (m : ℕ) :
    realSeqLiminfEReal (fun n => a (n + m)) = realSeqLiminfEReal a := by
  change seqLiminf (fun n => (a (n + m) : EReal)) =
    seqLiminf (fun n => (a n : EReal))
  rw [seqLiminf_eq_filter_liminf, seqLiminf_eq_filter_liminf]
  exact Filter.liminf_nat_add (fun n => (a n : EReal)) m

/-- Deleting the first term preserves finite-real limsup. -/
theorem realSeqLimsup_dropFirst (a : ℕ → ℝ) :
    realSeqLimsup (dropFirst a) = realSeqLimsup a := by
  change realSeqLimsup (fun n => a (n + 1)) = realSeqLimsup a
  exact realSeqLimsup_nat_add a 1

/-- Deleting the first term preserves finite-real liminf. -/
theorem realSeqLiminf_dropFirst (a : ℕ → ℝ) :
    realSeqLiminf (dropFirst a) = realSeqLiminf a := by
  change realSeqLiminf (fun n => a (n + 1)) = realSeqLiminf a
  exact realSeqLiminf_nat_add a 1

/-- Deleting the first term preserves total extended-real limsup. -/
theorem realSeqLimsupEReal_dropFirst (a : ℕ → ℝ) :
    realSeqLimsupEReal (dropFirst a) = realSeqLimsupEReal a := by
  change realSeqLimsupEReal (fun n => a (n + 1)) = realSeqLimsupEReal a
  exact realSeqLimsupEReal_nat_add a 1

/-- Deleting the first term preserves total extended-real liminf. -/
theorem realSeqLiminfEReal_dropFirst (a : ℕ → ℝ) :
    realSeqLiminfEReal (dropFirst a) = realSeqLiminfEReal a := by
  change realSeqLiminfEReal (fun n => a (n + 1)) = realSeqLiminfEReal a
  exact realSeqLiminfEReal_nat_add a 1

/-- Aggregate source-facing contract for Definition 4.3. -/
theorem def_4_3_limsup_liminf :
    (∀ a : ℕ → EReal,
      seqLimsup a = Filter.limsup a Filter.atTop ∧
      seqLiminf a = Filter.liminf a Filter.atTop) ∧
    (∀ a : ℕ → ℝ,
      realSeqLiminfEReal a ≤ realSeqLimsupEReal a) ∧
    (∀ a : PNat → ℝ,
      realSeqLimsupEReal (oneBasedToZeroBased a) =
          ⨅ j : PNat, ⨆ k : PNat, ⨆ (_hjk : j ≤ k), (a k : EReal) ∧
      realSeqLiminfEReal (oneBasedToZeroBased a) =
          ⨆ j : PNat, ⨅ k : PNat, ⨅ (_hjk : j ≤ k), (a k : EReal)) := by
  refine ⟨?_, realSeqLiminfEReal_le_realSeqLimsupEReal, ?_⟩
  · intro a
    exact ⟨seqLimsup_eq_filter_limsup a, seqLiminf_eq_filter_liminf a⟩
  · intro a
    exact
      ⟨realSeqLimsupEReal_oneBased_eq_iInf_iSup a,
        realSeqLiminfEReal_oneBased_eq_iSup_iInf a⟩
