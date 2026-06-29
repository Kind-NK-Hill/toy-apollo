/-
TASK ID: prob_14_8_montel_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.prob_14_8_subseq_support

open Filter MeasureTheory Set ProbabilityTheory
open scoped Topology Uniformity

noncomputable section

theorem prob_14_8_pointwise_relative_compact_of_bound
    {ι : Type*} {F : ι → ℂ → ℂ} {z : ℂ} {C : ℝ}
    (hbound : ∀ i, ‖F i z‖ ≤ C) :
    IsCompact (closure (Set.range fun i => F i z)) := by
  have hrange_subset :
      Set.range (fun i => F i z) ⊆ Metric.closedBall (0 : ℂ) C := by
    rintro w ⟨i, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hbound i
  exact (isCompact_closedBall (0 : ℂ) C).closure_of_subset hrange_subset

theorem prob_14_8_boundedContinuous_ascoli_closedBall
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {A : Set (BoundedContinuousFunction α ℂ)} {C : ℝ}
    (hbound : ∀ f x, f ∈ A → ‖f x‖ ≤ C)
    (h_eqcont : Equicontinuous ((↑) : A → α → ℂ)) :
    IsCompact (closure A) := by
  refine BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : ℂ) C)
    (isCompact_closedBall (0 : ℂ) C) A ?_ h_eqcont
  intro f x hf
  simpa [Metric.mem_closedBall, dist_eq_norm] using hbound f x hf

theorem prob_14_8_compact_closure_subseq
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {A : Set X} {u : ℕ → X}
    (hcompact : IsCompact (closure A))
    (hu : ∀ n, u n ∈ A) :
    ∃ f ∈ closure A, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 f) := by
  exact hcompact.tendsto_subseq (fun n => subset_closure (hu n))

theorem prob_14_8_boundedContinuous_ascoli_subseq
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {A : Set (BoundedContinuousFunction α ℂ)} {C : ℝ}
    {u : ℕ → BoundedContinuousFunction α ℂ}
    (hbound : ∀ f x, f ∈ A → ‖f x‖ ≤ C)
    (h_eqcont : Equicontinuous ((↑) : A → α → ℂ))
    (hu : ∀ n, u n ∈ A) :
    ∃ f ∈ closure A, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 f) := by
  exact prob_14_8_compact_closure_subseq
    (prob_14_8_boundedContinuous_ascoli_closedBall hbound h_eqcont) hu

theorem prob_14_8_boundedContinuous_ascoli_tendstoUniformly_subseq
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {A : Set (BoundedContinuousFunction α ℂ)} {C : ℝ}
    {u : ℕ → BoundedContinuousFunction α ℂ}
    (hbound : ∀ f x, f ∈ A → ‖f x‖ ≤ C)
    (h_eqcont : Equicontinuous ((↑) : A → α → ℂ))
    (hu : ∀ n, u n ∈ A) :
    ∃ f ∈ closure A, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformly (fun n x => u (φ n) x) f atTop := by
  obtain ⟨f, hf, φ, hφ, hlim⟩ :=
    prob_14_8_boundedContinuous_ascoli_subseq hbound h_eqcont hu
  exact ⟨f, hf, φ, hφ,
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim)⟩

theorem prob_14_8_tendstoUniformlyOn_subseq
    {α β : Type*} [UniformSpace β]
    {F : ℕ → α → β} {f : α → β} {K : Set α} {φ τ : ℕ → ℕ}
    (_hφ : StrictMono φ) (hτ : StrictMono τ)
    (hlim : TendstoUniformlyOn (fun n x => F (φ n) x) f atTop K) :
    TendstoUniformlyOn (fun n x => F (φ (τ n)) x) f atTop K := by
  exact hlim.seq_tendstoUniformlyOn τ hτ.tendsto_atTop

theorem prob_14_8_compactExhaustion_uniformOn_to_locallyUniform_subseq
    {α β : Type*} [TopologicalSpace α] [LocallyCompactSpace α] [UniformSpace β]
    (K : CompactExhaustion α) {F : ℕ → α → β} {f : α → β} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hK : ∀ n, TendstoUniformlyOn (fun k x => F (φ k) x) f atTop (K n)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoLocallyUniformly (fun k x => F (ψ k) x) f atTop := by
  refine ⟨φ, hφ, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro C hC
  obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hC
  exact (hK n).mono hn

def prob_14_8_diagTailIndex (tau : ℕ → ℕ → ℕ) (m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => tau m (prob_14_8_diagTailIndex tau (m + 1) k)

lemma prob_14_8_diagTailIndex_lt_succ
    {tau : ℕ → ℕ → ℕ} (htau : ∀ m, StrictMono (tau m)) :
    ∀ m k : ℕ,
      prob_14_8_diagTailIndex tau m k <
        prob_14_8_diagTailIndex tau m (k + 1) := by
  intro m k
  induction k generalizing m with
  | zero =>
      simp only [prob_14_8_diagTailIndex]
      exact lt_of_lt_of_le (Nat.lt_succ_self m)
        ((StrictMono.id_le (htau m)) (m + 1))
  | succ k ih =>
      simp only [prob_14_8_diagTailIndex]
      exact (htau m) (ih (m + 1))

lemma prob_14_8_diagTailIndex_eq
    {phi tau : ℕ → ℕ → ℕ}
    (hnest : ∀ m n, phi (m + 1) n = phi m (tau m n)) :
    ∀ m k : ℕ,
      phi (m + k) (m + k) =
        phi m (prob_14_8_diagTailIndex tau m k) := by
  intro m k
  induction k generalizing m with
  | zero =>
      simp [prob_14_8_diagTailIndex]
  | succ k ih =>
      calc
        phi (m + (k + 1)) (m + (k + 1))
            = phi ((m + 1) + k) ((m + 1) + k) := by
                simp [Nat.add_comm, Nat.add_left_comm]
        _ = phi (m + 1) (prob_14_8_diagTailIndex tau (m + 1) k) :=
            ih (m + 1)
        _ = phi m (tau m (prob_14_8_diagTailIndex tau (m + 1) k)) :=
            hnest m (prob_14_8_diagTailIndex tau (m + 1) k)
        _ = phi m (prob_14_8_diagTailIndex tau m (k + 1)) := by
            rfl

theorem prob_14_8_nested_subseq_diagonal_index
    {phi tau : ℕ → ℕ → ℕ}
    (hphi : ∀ m, StrictMono (phi m))
    (htau : ∀ m, StrictMono (tau m))
    (hnest : ∀ m n, phi (m + 1) n = phi m (tau m n)) :
    StrictMono (fun n : ℕ => phi n n) ∧
      ∀ m : ℕ, ∃ eta : ℕ → ℕ, StrictMono eta ∧
        ∀ k : ℕ, phi (m + k) (m + k) = phi m (eta k) := by
  constructor
  · refine strictMono_nat_of_lt_succ ?_
    intro n
    change phi n n < phi (n + 1) (n + 1)
    rw [hnest n (n + 1)]
    exact hphi n <| lt_of_lt_of_le (Nat.lt_succ_self n)
      ((StrictMono.id_le (htau n)) (n + 1))
  · intro m
    refine ⟨prob_14_8_diagTailIndex tau m, ?_, ?_⟩
    · exact strictMono_nat_of_lt_succ
        (prob_14_8_diagTailIndex_lt_succ htau m)
    · exact prob_14_8_diagTailIndex_eq hnest m

theorem prob_14_8_tendstoUniformlyOn_of_add
    {α β : Type*} [UniformSpace β]
    {G : ℕ → α → β} {f : α → β} {K : Set α} (m : ℕ)
    (h : TendstoUniformlyOn (fun k x => G (k + m) x) f atTop K) :
    TendstoUniformlyOn G f atTop K := by
  intro u hu
  rcases eventually_atTop.1 (h u hu) with ⟨N, hN⟩
  refine eventually_atTop.2 ⟨N + m, ?_⟩
  intro n hn x hx
  have hNm : N ≤ n - m := by omega
  have hsub : n - m + m = n := by omega
  simpa [hsub] using hN (n - m) hNm x hx

theorem prob_14_8_nested_uniformOn_to_locallyUniform_diagonal
    {α β : Type*} [TopologicalSpace α] [LocallyCompactSpace α] [UniformSpace β]
    (K : CompactExhaustion α) {F : ℕ → α → β} {f : α → β}
    {phi tau : ℕ → ℕ → ℕ}
    (hphi : ∀ m, StrictMono (phi m))
    (htau : ∀ m, StrictMono (tau m))
    (hnest : ∀ m n, phi (m + 1) n = phi m (tau m n))
    (hlim : ∀ m,
      TendstoUniformlyOn (fun n x => F (phi m n) x) f atTop (K m)) :
    ∃ psi : ℕ → ℕ, StrictMono psi ∧
      TendstoLocallyUniformly (fun n x => F (psi n) x) f atTop := by
  let psi : ℕ → ℕ := fun n => phi n n
  have hdiag_full :=
    prob_14_8_nested_subseq_diagonal_index
      (hphi := hphi) (htau := htau) (hnest := hnest)
  have hpsi : StrictMono psi := hdiag_full.1
  have htail := hdiag_full.2
  have hK : ∀ m,
      TendstoUniformlyOn (fun k x => F (psi k) x) f atTop (K m) := by
    intro m
    rcases htail m with ⟨eta, heta, heq⟩
    have hsub :
        TendstoUniformlyOn (fun k x => F (phi m (eta k)) x) f atTop (K m) :=
      prob_14_8_tendstoUniformlyOn_subseq (hphi m) heta (hlim m)
    have hshift :
        TendstoUniformlyOn (fun k x => F (psi (k + m)) x) f atTop (K m) := by
      refine hsub.congr (Filter.Eventually.of_forall ?_)
      intro k x hx
      change F (phi m (eta k)) x = F (phi (k + m) (k + m)) x
      rw [Nat.add_comm k m]
      rw [heq k]
    exact prob_14_8_tendstoUniformlyOn_of_add m hshift
  exact prob_14_8_compactExhaustion_uniformOn_to_locallyUniform_subseq K hpsi hK

theorem prob_14_8_nested_stageLimits_to_locallyUniform_diagonal
    {α β : Type*} [TopologicalSpace α] [LocallyCompactSpace α]
    [UniformSpace β] [T2Space β]
    (K : CompactExhaustion α) {F : ℕ → α → β}
    {phi tau : ℕ → ℕ → ℕ} {fstage : ∀ m : ℕ, K m → β}
    (hphi : ∀ m, StrictMono (phi m))
    (htau : ∀ m, StrictMono (tau m))
    (hnest : ∀ m n, phi (m + 1) n = phi m (tau m n))
    (hlim :
      ∀ m : ℕ,
        TendstoUniformly
          (fun n (x : K m) => F (phi m n) x)
          (fstage m) atTop) :
    ∃ f : α → β, ∃ psi : ℕ → ℕ, StrictMono psi ∧
      TendstoLocallyUniformly (fun n x => F (psi n) x) f atTop := by
  classical
  let f : α → β := fun x =>
    fstage (K.find x) ⟨x, K.mem_find x⟩
  have hadj :
      ∀ m : ℕ, ∀ x : K m,
        fstage m x =
          fstage (m + 1) ⟨(x : α), K.subset_succ m x.property⟩ := by
    intro m x
    have hleft :
        Tendsto
          (fun n : ℕ => F (phi m (tau m n)) (x : α))
          atTop
          (𝓝 (fstage m x)) :=
      ((hlim m).tendsto_at x).comp (htau m).tendsto_atTop
    have hright :
        Tendsto
          (fun n : ℕ => F (phi m (tau m n)) (x : α))
          atTop
          (𝓝 (fstage (m + 1) ⟨(x : α), K.subset_succ m x.property⟩)) := by
      have hraw :
          Tendsto
            (fun n : ℕ => F (phi (m + 1) n)
              (⟨(x : α), K.subset_succ m x.property⟩ : K (m + 1)))
            atTop
            (𝓝 (fstage (m + 1)
              ⟨(x : α), K.subset_succ m x.property⟩)) :=
        (hlim (m + 1)).tendsto_at
          ⟨(x : α), K.subset_succ m x.property⟩
      simpa [hnest m] using hraw
    exact tendsto_nhds_unique hleft hright
  have hstage_eq_add :
      ∀ n r : ℕ, ∀ x : K r,
        fstage r x =
          fstage (r + n)
            ⟨(x : α), K.subset (Nat.le_add_right r n) x.property⟩ := by
    intro n
    induction n with
    | zero =>
        intro r x
        simp
    | succ n ih =>
        intro r x
        have h1 := ih r x
        have h2 := hadj (r + n)
          (⟨(x : α), K.subset (Nat.le_add_right r n) x.property⟩ : K (r + n))
        calc
          fstage r x =
              fstage (r + n)
                ⟨(x : α), K.subset (Nat.le_add_right r n) x.property⟩ := h1
          _ = fstage (r + n + 1)
                ⟨(x : α),
                  K.subset (by omega : r ≤ r + n + 1) x.property⟩ := by
                simpa [Nat.add_assoc] using h2
  have hstage_eq_of_le :
      ∀ {r m : ℕ} (hrm : r ≤ m) (x : K r),
        fstage r x =
          fstage m ⟨(x : α), K.subset hrm x.property⟩ := by
    intro r m hrm x
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hrm
    exact hstage_eq_add n r x
  have hEqStage :
      ∀ m : ℕ, ∀ x : α, ∀ hx : x ∈ K m,
        f x = fstage m ⟨x, hx⟩ := by
    intro m x hx
    have hfind_le : K.find x ≤ m := (K.mem_iff_find_le).1 hx
    have h :=
      hstage_eq_of_le hfind_le
        (⟨x, K.mem_find x⟩ : K (K.find x))
    simpa [f] using h
  have hlim_global :
      ∀ m : ℕ,
        TendstoUniformlyOn
          (fun n x => F (phi m n) x)
          f atTop (K m) := by
    intro m u hu
    filter_upwards [hlim m u hu] with n hn x hx
    have hfx : f x = fstage m ⟨x, hx⟩ := hEqStage m x hx
    simpa [hfx] using hn ⟨x, hx⟩
  obtain ⟨psi, hpsi, hloc⟩ :=
    prob_14_8_nested_uniformOn_to_locallyUniform_diagonal
      K hphi htau hnest hlim_global
  exact ⟨f, psi, hpsi, hloc⟩

theorem prob_14_8_uniformOn_subseq_limit_eqOn
    {α β : Type*} [TopologicalSpace α] [UniformSpace β] [T2Space β]
    {F : ℕ → α → β} {f g : α → β} {K L : Set α} {tau : ℕ → ℕ}
    (htau : StrictMono tau)
    (hK : TendstoUniformlyOn F f atTop K)
    (hL : TendstoUniformlyOn (fun n x => F (tau n) x) g atTop L)
    (hKL : K ⊆ L) :
    Set.EqOn f g K := by
  intro x hx
  have hfx : Tendsto (fun n => F (tau n) x) atTop (𝓝 (f x)) :=
    (hK.seq_tendstoUniformlyOn tau htau.tendsto_atTop).tendsto_at hx
  have hgx : Tendsto (fun n => F (tau n) x) atTop (𝓝 (g x)) :=
    hL.tendsto_at (hKL hx)
  exact tendsto_nhds_unique hfx hgx

def prob_14_8_compactStageBCF
    {ι : Type*} (F : ι → ℂ → ℂ) {K U : Set ℂ}
    (hK : IsCompact K)
    (hKU : K ⊆ U)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) U) :
    ι → BoundedContinuousFunction K ℂ := by
  intro i
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  refine BoundedContinuousFunction.mkOfCompact ?_
  refine ⟨fun x : K => F i x, ?_⟩
  exact (((hF i).continuousOn).mono hKU).restrict

@[simp]
lemma prob_14_8_compactStageBCF_apply
    {ι : Type*} {F : ι → ℂ → ℂ} {K U : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) U)
    (i : ι) (x : K) :
    prob_14_8_compactStageBCF F hK hKU hF i x = F i x := rfl

theorem prob_14_8_analytic_cthickening_bound_equicontinuousOn
    {ι : Type*} {F : ι → ℂ → ℂ} {U K : Set ℂ} {δ M : ℝ}
    (hδ : 0 < δ)
    (hM : 0 ≤ M)
    (hthick : Metric.cthickening δ K ⊆ U)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) U)
    (hbound : ∀ i z, z ∈ Metric.cthickening δ K → ‖F i z‖ ≤ M) :
    EquicontinuousOn F K := by
  intro x0 hx0
  refine (Metric.equicontinuousAt_iff.mpr ?_).equicontinuousWithinAt K
  intro ε hε
  let A : ℝ := (2 * M) / δ
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (mul_nonneg (by norm_num) hM) hδ.le
  obtain ⟨q, hq_pos, hq_mul⟩ : ∃ q : ℝ, 0 < q ∧ A * q < ε :=
    exists_pos_mul_lt hε A
  refine ⟨min δ q, lt_min hδ hq_pos, ?_⟩
  intro x hx i
  have hxδ : dist x x0 < δ := lt_of_lt_of_le hx (min_le_left _ _)
  have hxq : dist x x0 < q := lt_of_lt_of_le hx (min_le_right _ _)
  have hball_subset_thick :
      Metric.ball x0 δ ⊆ Metric.cthickening δ K := by
    intro z hz
    exact Metric.mem_cthickening_of_dist_le z x0 δ K hx0 (le_of_lt hz)
  have hball_subset_U : Metric.ball x0 δ ⊆ U :=
    hball_subset_thick.trans hthick
  have hd : DifferentiableOn ℂ (F i) (Metric.ball x0 δ) :=
    (hF i).analyticOn.differentiableOn.mono hball_subset_U
  have hx0_thick : x0 ∈ Metric.cthickening δ K :=
    Metric.self_subset_cthickening (δ := δ) K hx0
  have hmaps :
      MapsTo (F i) (Metric.ball x0 δ) (Metric.closedBall (F i x0) (2 * M)) := by
    intro z hz
    have hz_thick : z ∈ Metric.cthickening δ K := hball_subset_thick hz
    calc
      dist (F i z) (F i x0) ≤ ‖F i z‖ + ‖F i x0‖ :=
        dist_le_norm_add_norm _ _
      _ ≤ M + M := add_le_add (hbound i z hz_thick) (hbound i x0 hx0_thick)
      _ = 2 * M := by ring
  have hx_ball : x ∈ Metric.ball x0 δ := by
    simpa using hxδ
  have hschwarz :
      dist (F i x0) (F i x) ≤ A * dist x x0 := by
    have h :=
      Complex.dist_le_div_mul_dist_of_mapsTo_ball
        (f := F i) (c := x0) (R₁ := δ) (R₂ := 2 * M) (z := x)
        hd hmaps hx_ball
    simpa [A, dist_comm] using h
  have hprod_le : A * dist x x0 ≤ A * q :=
    mul_le_mul_of_nonneg_left (le_of_lt hxq) hA_nonneg
  exact hschwarz.trans_lt (hprod_le.trans_lt hq_mul)

theorem prob_14_8_compactStageBCF_ascoli_inputs
    {ι : Type*} {F : ι → ℂ → ℂ} {U K : Set ℂ} {δ M : ℝ}
    (hK : IsCompact K)
    (hδ : 0 < δ)
    (hM : 0 ≤ M)
    (hthick : Metric.cthickening δ K ⊆ U)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) U)
    (hbound : ∀ i z, z ∈ Metric.cthickening δ K → ‖F i z‖ ≤ M) :
    let u : ι → BoundedContinuousFunction K ℂ :=
      prob_14_8_compactStageBCF F hK
        (fun _ hz => hthick (Metric.self_subset_cthickening (δ := δ) K hz)) hF
    (∀ f x, f ∈ Set.range u → ‖f x‖ ≤ M) ∧
      Equicontinuous ((↑) : Set.range u → K → ℂ) := by
  dsimp only
  let hKU : K ⊆ U :=
    fun _ hz => hthick (Metric.self_subset_cthickening (δ := δ) K hz)
  let u : ι → BoundedContinuousFunction K ℂ :=
    prob_14_8_compactStageBCF F hK hKU hF
  have hEqOn : EquicontinuousOn F K :=
    prob_14_8_analytic_cthickening_bound_equicontinuousOn
      hδ hM hthick hF hbound
  constructor
  · intro f x hf
    rcases hf with ⟨i, hi⟩
    rw [← hi]
    exact hbound i x (Metric.self_subset_cthickening (δ := δ) K x.property)
  · have hres : Equicontinuous (fun i : ι => K.restrict (F i)) :=
      (equicontinuous_restrict_iff F).2 hEqOn
    intro x0 V hV
    filter_upwards [hres x0 V hV] with x hx a
    rcases a.property with ⟨i, hi⟩
    rw [← hi]
    exact hx i

theorem prob_14_8_compactStage_subseq_from_analytic_compact_bounds
    {F : ℕ → ℂ → ℂ} {U K : Set ℂ}
    (hU : IsOpen U)
    (hK : IsCompact K)
    (hKU : K ⊆ U)
    (hF : ∀ n : ℕ, AnalyticOnNhd ℂ (F n) U)
    (hbound :
      ∀ K' : Set ℂ, IsCompact K' → K' ⊆ U →
        ∃ C : ℝ, ∀ n : ℕ, ∀ z : ℂ, z ∈ K' → ‖F n z‖ ≤ C) :
    ∃ f : K → ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun n (x : K) => F (φ n) x) f atTop := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_cthickening_subset_open hU hKU
  have hKthick : IsCompact (Metric.cthickening δ K) := hK.cthickening
  obtain ⟨C, hC⟩ := hbound (Metric.cthickening δ K) hKthick hthick
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right C 0
  have hboundM : ∀ n : ℕ, ∀ z : ℂ,
      z ∈ Metric.cthickening δ K → ‖F n z‖ ≤ M := by
    intro n z hz
    exact (hC n z hz).trans (le_max_left C 0)
  have hinputs :=
    prob_14_8_compactStageBCF_ascoli_inputs
      (F := F) (U := U) (K := K) (δ := δ) (M := M)
      hK hδ hM hthick hF hboundM
  let u : ℕ → BoundedContinuousFunction K ℂ :=
    prob_14_8_compactStageBCF F hK hKU hF
  obtain ⟨f, _hf, φ, hφ, hlim⟩ :=
    prob_14_8_boundedContinuous_ascoli_tendstoUniformly_subseq
      (A := Set.range u) (C := M) hinputs.1 hinputs.2
      (fun n => ⟨n, rfl⟩)
  exact ⟨fun x => f x, φ, hφ, by simpa [u] using hlim⟩

theorem prob_14_8_compactStage_subseq_on_open_subtype
    {F : ℕ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ n : ℕ, AnalyticOnNhd ℂ (F n) U)
    (hbound :
      ∀ K' : Set ℂ, IsCompact K' → K' ⊆ U →
        ∃ C : ℝ, ∀ n : ℕ, ∀ z : ℂ, z ∈ K' → ‖F n z‖ ≤ C)
    {K : Set U} (hK : IsCompact K)
    {φ : ℕ → ℕ} (_hφ : StrictMono φ) :
    ∃ f : K → ℂ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoUniformly
        (fun n (x : K) => F (φ (ψ n)) (x : U))
        f atTop := by
  let L : Set ℂ := Subtype.val '' K
  have hL : IsCompact L := hK.image continuous_subtype_val
  have hLU : L ⊆ U := by
    intro z hz
    rcases hz with ⟨x, _hx, rfl⟩
    exact x.property
  have hFφ : ∀ n : ℕ, AnalyticOnNhd ℂ (fun z : ℂ => F (φ n) z) U :=
    fun n => hF (φ n)
  have hboundφ :
      ∀ K' : Set ℂ, IsCompact K' → K' ⊆ U →
        ∃ C : ℝ, ∀ n : ℕ, ∀ z : ℂ,
          z ∈ K' → ‖F (φ n) z‖ ≤ C := by
    intro K' hK' hK'U
    rcases hbound K' hK' hK'U with ⟨C, hC⟩
    exact ⟨C, fun n z hz => hC (φ n) z hz⟩
  obtain ⟨fL, ψ, hψ, hlimL⟩ :=
    prob_14_8_compactStage_subseq_from_analytic_compact_bounds
      (F := fun n z => F (φ n) z) (U := U) (K := L)
      hU hL hLU hFφ hboundφ
  let g : K → L := fun x =>
    ⟨(x : U), ⟨(x : U), x.property, rfl⟩⟩
  refine ⟨fun x => fL (g x), ψ, hψ, ?_⟩
  simpa [g, Function.comp_def] using hlimL.comp g

theorem prob_14_8_montel_subseq_of_analytic_compact_bounds
    {F : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U)
    (hF : ∀ n : ℕ, AnalyticOnNhd ℂ (F n) U)
    (hbound :
      ∀ K' : Set ℂ, IsCompact K' → K' ⊆ U →
        ∃ C : ℝ, ∀ n : ℕ, ∀ z : ℂ, z ∈ K' → ‖F n z‖ ≤ C) :
    ∃ f : ℂ → ℂ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoLocallyUniformlyOn
        (fun k z => F (ψ k) z) f atTop U := by
  classical
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  let Kex : CompactExhaustion U := CompactExhaustion.choice U
  let stageExists :
      (m : ℕ) → (st : {θ : ℕ → ℕ // StrictMono θ}) →
        ∃ f : Kex m → ℂ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          TendstoUniformly
            (fun n (x : Kex m) => F (st.1 (ψ n)) (x : U))
            f atTop :=
    fun m st =>
      prob_14_8_compactStage_subseq_on_open_subtype
        (F := F) (U := U) hU hF hbound
        (K := Kex m) (Kex.isCompact m) (φ := st.1) st.2
  let step (m : ℕ) (st : {θ : ℕ → ℕ // StrictMono θ}) :
      {θ : ℕ → ℕ // StrictMono θ} :=
    let ex := stageExists m st
    let ex' := Classical.choose_spec ex
    let ψ := Classical.choose ex'
    let hψ : StrictMono ψ := (Classical.choose_spec ex').1
    ⟨fun n => st.1 (ψ n), st.2.comp hψ⟩
  let preState : ℕ → {θ : ℕ → ℕ // StrictMono θ} :=
    fun m => Nat.rec ⟨id, strictMono_id⟩ (fun m st => step m st) m
  let tauStage : ℕ → ℕ → ℕ := fun m =>
    Classical.choose (Classical.choose_spec (stageExists m (preState m)))
  let phi : ℕ → ℕ → ℕ := fun m => (preState (m + 1)).1
  let tau : ℕ → ℕ → ℕ := fun m => tauStage (m + 1)
  let fstage : ∀ m : ℕ, Kex m → ℂ := fun m =>
    Classical.choose (stageExists m (preState m))
  have hphi : ∀ m : ℕ, StrictMono (phi m) :=
    fun m => (preState (m + 1)).2
  have htau : ∀ m : ℕ, StrictMono (tau m) := by
    intro m
    dsimp [tau, tauStage]
    exact (Classical.choose_spec
      (Classical.choose_spec (stageExists (m + 1) (preState (m + 1))))).1
  have hnest : ∀ m n : ℕ, phi (m + 1) n = phi m (tau m n) := by
    intro m n
    rfl
  have hlim :
      ∀ m : ℕ,
        TendstoUniformly
          (fun n (x : Kex m) => F (phi m n) (x : U))
          (fstage m) atTop := by
    intro m
    dsimp [phi, fstage, preState, step, tauStage]
    exact (Classical.choose_spec
      (Classical.choose_spec (stageExists m (preState m)))).2
  obtain ⟨fU, ψ, hψ, hlocU⟩ :=
    prob_14_8_nested_stageLimits_to_locallyUniform_diagonal
      (K := Kex) (F := fun n (x : U) => F n x)
      hphi htau hnest hlim
  let f : ℂ → ℂ := fun z =>
    if hz : z ∈ U then fU ⟨z, hz⟩ else 0
  refine ⟨f, ψ, hψ, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  change TendstoLocallyUniformly
    (fun i (x : U) => F (ψ i) x) (fun x : U => f (x : ℂ)) atTop
  simpa [f] using hlocU

theorem prob_14_8_identity_eqOn_of_accumulating_sequence
    {f g : ℂ → ℂ} {U : Set ℂ} {z0 : ℂ} {a : ℕ → ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U)
    (hz0 : z0 ∈ U)
    (ha_lim : Tendsto a atTop (𝓝 z0))
    (ha_ne : ∀ n : ℕ, a n ≠ z0)
    (ha_eq : ∀ n : ℕ, f (a n) = g (a n)) :
    Set.EqOn f g U := by
  have ha_within :
      Tendsto a atTop (nhdsWithin z0 ({z0} : Set ℂ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact ha_lim
    · exact Filter.Eventually.of_forall (by
        intro n
        exact Set.mem_compl (by simpa using ha_ne n))
  have hfreq_atTop :
      ∃ᶠ n : ℕ in atTop, f (a n) = g (a n) :=
    Filter.Frequently.of_forall ha_eq
  have hfreq :
      ∃ᶠ z : ℂ in nhdsWithin z0 ({z0} : Set ℂ)ᶜ, f z = g z :=
    ha_within.frequently hfreq_atTop
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hU hz0 hfreq

theorem prob_14_8_accumulation_identity_adapter
    {f g : ℂ → ℂ} {U : Set ℂ} {z0 : ℂ} {a : ℕ → ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U)
    (hz0 : z0 ∈ U)
    (ha_lim : Tendsto a atTop (𝓝 z0))
    (ha_ne : ∀ n : ℕ, a n ≠ z0)
    (ha_eq : ∀ n : ℕ, f (a n) = g (a n)) :
    Set.EqOn f g U :=
  prob_14_8_identity_eqOn_of_accumulating_sequence
    hf hg hU hz0 ha_lim ha_ne ha_eq

theorem prob_14_8_locally_uniform_subseq_limit_eqOn_of_real_axis
    {F : ℕ → ℂ → ℂ} {f g : ℂ → ℂ} {U : Set ℂ}
    {φ : ℕ → ℕ} {z0 : ℂ} {a : ℕ → ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U)
    (hz0 : z0 ∈ U)
    (hφ : StrictMono φ)
    (hlim :
      TendstoLocallyUniformlyOn
        (fun k z => F (φ k) z) f atTop U)
    (ha_lim : Tendsto a atTop (𝓝 z0))
    (ha_ne : ∀ n : ℕ, a n ≠ z0)
    (ha_mem : ∀ n : ℕ, a n ∈ U)
    (ha_conv :
      ∀ n : ℕ, Tendsto (fun k : ℕ => F k (a n)) atTop (𝓝 (g (a n)))) :
    Set.EqOn f g U := by
  refine prob_14_8_accumulation_identity_adapter
    hf hg hU hz0 ha_lim ha_ne ?_
  intro n
  have hlimit_from_subseq :
      Tendsto (fun k : ℕ => F (φ k) (a n)) atTop (𝓝 (f (a n))) :=
    hlim.tendsto_at (ha_mem n)
  have hlimit_from_real_axis :
      Tendsto (fun k : ℕ => F (φ k) (a n)) atTop (𝓝 (g (a n))) :=
    (ha_conv n).comp hφ.tendsto_atTop
  exact tendsto_nhds_unique hlimit_from_subseq hlimit_from_real_axis

theorem prob_14_8_locally_uniform_limit_of_analytic_is_analytic
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U)
    (hF : ∀ᶠ n : ℕ in atTop, AnalyticOnNhd ℂ (F n) U)
    (hlim : TendstoLocallyUniformlyOn F f atTop U) :
    AnalyticOnNhd ℂ f U := by
  have hFDiff : ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (F n) U := by
    filter_upwards [hF] with n hn
    exact hn.analyticOn.differentiableOn
  have hdiff : DifferentiableOn ℂ f U :=
    hlim.differentiableOn hFDiff hU
  exact hdiff.analyticOnNhd hU
