import Mathlib

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology BigOperators

section IIDWord

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]
variable {n : ℕ} [NeZero n]

/-- Uniform measure on a finite alphabet. -/
noncomputable def alphabetMeasure : Measure α :=
  (PMF.uniformOfFintype α).toMeasure

@[simp] lemma alphabetMeasure_apply_singleton (a : α) :
    alphabetMeasure ({a} : Set α) = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simpa [alphabetMeasure] using
    (PMF.toMeasure_uniformOfFintype_apply
      (α := α) (s := ({a} : Set α)) (measurableSet_singleton a))

instance : IsProbabilityMeasure (alphabetMeasure (α := α)) := by
  dsimp [alphabetMeasure]
  infer_instance

/-- The product measure for an infinite iid uniformly random string over the alphabet. -/
noncomputable def typingMeasure : Measure (ℕ → α) :=
  Measure.infinitePi fun _ : ℕ => alphabetMeasure (α := α)

instance : IsProbabilityMeasure (typingMeasure (α := α)) := by
  dsimp [typingMeasure]
  infer_instance

/-- The `k`-th non-overlapping block of length `n`, using zero-based block indices. -/
def blockMap (n : ℕ) (k : ℕ) (x : ℕ → α) : Fin n → α :=
  fun i => x (k * n + i)

/-- The event that the `k`-th block is exactly the word `w`. -/
def wordEvent (n : ℕ) (w : Fin n → α) (k : ℕ) : Set (ℕ → α) :=
  blockMap (α := α) n k ⁻¹' {w}

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] [NeZero n] in
lemma measurable_blockMap (k : ℕ) : Measurable (blockMap (α := α) n k) := by
  rw [measurable_pi_iff]
  intro i
  simpa [blockMap] using measurable_pi_apply (k * n + i)

omit [Fintype α] [Nonempty α] [NeZero n] in
lemma measurableSet_wordEvent (w : Fin n → α) (k : ℕ) :
    MeasurableSet (wordEvent (α := α) n w k) := by
  exact measurable_blockMap (α := α) (n := n) k (measurableSet_singleton w)

omit [MeasurableSingletonClass α] in
lemma typingMeasure_block_family_map :
    (typingMeasure (α := α)).map (fun x k i => blockMap (α := α) n k x i) =
      Measure.infinitePi
        (fun _ : ℕ => Measure.infinitePi (fun _ : Fin n => alphabetMeasure (α := α))) := by
  let e : ℕ ≃ ℕ × Fin n := Nat.divModEquiv n
  have h_reindex :
      (typingMeasure (α := α)).map
          (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Fin n => α) e) =
        Measure.infinitePi (fun _ : ℕ × Fin n => alphabetMeasure (α := α)) := by
    simpa [typingMeasure] using
      (Measure.infinitePi_map_piCongrLeft
        (μ := fun _ : ℕ × Fin n => alphabetMeasure (α := α)) (e := e))
  have h_curry :
      (Measure.infinitePi (fun _ : ℕ × Fin n => alphabetMeasure (α := α))).map
          (MeasurableEquiv.curry ℕ (Fin n) α) =
        Measure.infinitePi
          (fun _ : ℕ => Measure.infinitePi (fun _ : Fin n => alphabetMeasure (α := α))) := by
    simpa using
      (Measure.infinitePi_map_curry
        (μ := fun (_ : ℕ) (_ : Fin n) => alphabetMeasure (α := α)))
  calc
    (typingMeasure (α := α)).map (fun x k i => blockMap (α := α) n k x i) =
        Measure.map (MeasurableEquiv.curry ℕ (Fin n) α)
          (Measure.map (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Fin n => α) e)
            (typingMeasure (α := α))) := by
      have h_comp :
          ((MeasurableEquiv.curry ℕ (Fin n) α) ∘
            (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Fin n => α) e)) =
            fun x k i => blockMap (α := α) n k x i := by
        ext x k i
        change
          ((Equiv.piCongrLeft (fun _ : ℕ × Fin n => α) e) x) (k, i) =
            x (k * n + i)
        simpa [e] using
          (Equiv.piCongrLeft_apply_eq_cast
            (P := fun _ : ℕ × Fin n => α) (e := e) x (k, i))
      rw [← h_comp]
      symm
      exact Measure.map_map (by fun_prop) (by fun_prop)
    _ = Measure.infinitePi
          (fun _ : ℕ => Measure.infinitePi (fun _ : Fin n => alphabetMeasure (α := α))) := by
      rw [h_reindex, h_curry]

omit [MeasurableSingletonClass α] in
lemma typingMeasure_blockMap_distribution (k : ℕ) :
    (typingMeasure (α := α)).map (blockMap (α := α) n k) =
      Measure.infinitePi (fun _ : Fin n => alphabetMeasure (α := α)) := by
  have h_eval :=
    congrArg
      (fun ν => ν.map (fun f : ℕ → (Fin n → α) => f k))
      (typingMeasure_block_family_map (α := α) (n := n))
  change
    Measure.map (fun f : ℕ → Fin n → α => f k)
      (Measure.map (fun x k i => blockMap (α := α) n k x i) (typingMeasure (α := α))) =
      Measure.map (fun f : ℕ → Fin n → α => f k)
        (Measure.infinitePi
          (fun _ : ℕ => Measure.infinitePi (fun _ : Fin n => alphabetMeasure (α := α)))) at h_eval
  have h_left :
      Measure.map (fun f : ℕ → (Fin n → α) => f k)
          (Measure.map (fun x i j => blockMap (α := α) n i x j) (typingMeasure (α := α))) =
        Measure.map (blockMap (α := α) n k) (typingMeasure (α := α)) := by
    have h_family_meas : Measurable (fun x i j => blockMap (α := α) n i x j) := by
      rw [show (fun x i j => blockMap (α := α) n i x j) =
        fun x i j => x (i * n + j) by
        rfl]
      rw [measurable_pi_iff]
      intro i
      rw [measurable_pi_iff]
      intro j
      simpa using measurable_pi_apply (i * n + j)
    have h_eval_meas : Measurable (fun f : ℕ → (Fin n → α) => f k) := by
      exact measurable_pi_apply k
    have h_comp :
        ((fun f : ℕ → (Fin n → α) => f k) ∘
            (fun x i j => blockMap (α := α) n i x j)) =
          blockMap (α := α) n k := by
      rfl
    rw [Measure.map_map h_eval_meas h_family_meas, h_comp]
  rw [h_left, Measure.infinitePi_map_eval] at h_eval
  simpa [blockMap] using h_eval

omit [MeasurableSingletonClass α] in
lemma iIndepFun_blockMap :
    iIndepFun (blockMap (α := α) n) (typingMeasure (α := α)) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map]
  · calc
      (typingMeasure (α := α)).map (fun x k i => blockMap (α := α) n k x i) =
          Measure.infinitePi
            (fun _ : ℕ => Measure.infinitePi (fun _ : Fin n => alphabetMeasure (α := α))) :=
        typingMeasure_block_family_map (α := α) (n := n)
      _ =
          Measure.infinitePi
            (fun k : ℕ => (typingMeasure (α := α)).map (blockMap (α := α) n k)) := by
        have h_fun :
            (fun _ : ℕ => Measure.infinitePi (fun _ : Fin n => alphabetMeasure (α := α))) =
              (fun k : ℕ => (typingMeasure (α := α)).map (blockMap (α := α) n k)) := by
          funext k
          symm
          exact typingMeasure_blockMap_distribution (α := α) (n := n) k
        rw [h_fun]
  · intro k
    exact measurable_blockMap (α := α) (n := n) k

lemma iIndepSet_wordEvent (w : Fin n → α) :
    iIndepSet (wordEvent (α := α) n w) (typingMeasure (α := α)) := by
  refine (iIndepSet_iff_meas_biInter
    (f := wordEvent (α := α) n w)
    (μ := typingMeasure (α := α))
    (hf := measurableSet_wordEvent (α := α) (n := n) w)).2 ?_
  intro s
  simpa [wordEvent] using
    (iIndepFun_blockMap (α := α) (n := n)).measure_inter_preimage_eq_mul s
      (fun _ _ => measurableSet_singleton w)

lemma typingMeasure_wordEvent (w : Fin n → α) (k : ℕ) :
    typingMeasure (α := α) (wordEvent (α := α) n w k) =
      ((Fintype.card α : ℝ≥0∞)⁻¹) ^ n := by
  rw [wordEvent,
    ← Measure.map_apply (measurable_blockMap (α := α) (n := n) k) (measurableSet_singleton w),
    typingMeasure_blockMap_distribution (α := α) (n := n) k,
    Measure.infinitePi_singleton_of_fintype]
  simp [alphabetMeasure_apply_singleton, Finset.prod_const]

lemma tsum_wordEvent_eq_top (w : Fin n → α) :
    (∑' k, typingMeasure (α := α) (wordEvent (α := α) n w k)) = ∞ := by
  rw [show (∑' k, typingMeasure (α := α) (wordEvent (α := α) n w k)) =
      ∑' _ : ℕ, ((Fintype.card α : ℝ≥0∞)⁻¹) ^ n by
    congr with k
    exact typingMeasure_wordEvent (α := α) (n := n) w k]
  have h_nonzero : ((Fintype.card α : ℝ≥0∞)⁻¹) ^ n ≠ 0 := by
    exact pow_ne_zero _ (ENNReal.inv_ne_zero.2 (by simp : (Fintype.card α : ℝ≥0∞) ≠ ∞))
  exact ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) h_nonzero

/-- Every fixed finite word appears in infinitely many disjoint iid blocks almost surely. -/
theorem typingMeasure_limsup_wordEvent_eq_one (w : Fin n → α) :
    typingMeasure (α := α) (limsup (wordEvent (α := α) n w) atTop) = 1 := by
  exact ProbabilityTheory.measure_limsup_eq_one
    (hsm := measurableSet_wordEvent (α := α) (n := n) w)
    (hs := iIndepSet_wordEvent (α := α) (n := n) w)
    (hs' := tsum_wordEvent_eq_top (α := α) (n := n) w)

end IIDWord
