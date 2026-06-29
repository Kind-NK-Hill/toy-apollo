import Mathlib
import ToyApollo.Output.def_3_10

/-
TASK ID: prob_3_7
TYPE: Problem
SOURCE PLAN: 07_chap3_problems
TASK CONTENT:
\textbf{3.7.} (An alternate definition of $\lambda$-system) Show that the following three conditions are equivalent to the definition of $\lambda$-system in Definition 3.10:
\begin{enumerate}
    \item $\Omega \in \mathcal{L}$.
    \item If $A$ and $B$ are sets in $\mathcal{L}$ and $A \subseteq B$, then $B \setminus A \in \mathcal{L}$.
    \item If $A_1, A_2, A_3, \dots$ is a sequence of \textit{increasing} sets in $\mathcal{L}$, then \cup_{i=1}^{\infty} A_i \in \mathcal{L}$.
\end{enumerate}
-/

-- WRITE FINAL LEAN CODE BELOW

theorem prob_3_7 (Ω : Type _) (L : Set (Set Ω)) :
    LambdaSystem L ↔
    (Set.univ ∈ L ∧ (∀ A ∈ L, ∀ B ∈ L, A ⊆ B → B \ A ∈ L) ∧
     (∀ (f : ℕ → Set Ω), (∀ i, f i ∈ L) → Monotone f → ⋃ i, f i ∈ L)) := by
       constructor;
       · intro h
         let h_univ : Set.univ ∈ L := h.univ_mem
         let h_compl : ∀ A ∈ L, Aᶜ ∈ L := fun A hA => h.compl_mem hA
         let h_disjoint :
             ∀ (f : ℕ → Set Ω), Pairwise (Function.onFun Disjoint f) →
               (∀ i, f i ∈ L) → ⋃ i, f i ∈ L :=
           fun f hf hmem => h.iUnion_mem hf hmem
         constructor
         · exact h_univ
         generalize_proofs at *;
         constructor;
         · intro A hA B hB hAB
           have h_compl : Bᶜ ∪ A ∈ L := by
             convert h_disjoint ( fun i => if i = 0 then Bᶜ else if i = 1 then A else ∅ ) _ _ using 1 <;> simp_all +decide [ Pairwise ];
             · ext x; simp [Set.mem_union, Set.mem_iUnion];
               exact ⟨ fun hx => hx.elim ( fun hx => ⟨ 0, hx ⟩ ) fun hx => ⟨ 1, hx ⟩, fun ⟨ i, hi ⟩ => by rcases i with ( _ | _ | i ) <;> aesop ⟩;
             · grind +revert;
             · intro i; split_ifs <;> simp_all +decide [ Set.compl_def ] ;
               simpa using h_compl _ h_univ
           have h_compl' : (Bᶜ ∪ A)ᶜ ∈ L := by
             solve_by_elim
           have h_final : B \ A ∈ L := by
             convert h_compl' using 1 ; ext ; aesop
           exact h_final;
         · intro f hf hf_mono;
           convert h_disjoint ( fun i => if i = 0 then f 0 else f i \ f ( i - 1 ) ) _ _ using 1;
           · ext x;
             simp +decide [ Set.ext_iff ];
             constructor <;> rintro ⟨ i, hi ⟩;
             · induction' i with i ih;
               · exact ⟨ 0, hi ⟩;
               · grind +splitImp;
             · split_ifs at hi <;> [ exact ⟨ 0, hi ⟩ ; exact ⟨ i, hi.1 ⟩ ];
           · intro i j hij; rcases i with ( _ | i ) <;> rcases j with ( _ | j ) <;> simp_all +decide [ Set.disjoint_left ] ;
             · exact fun x hx₁ hx₂ => hf_mono ( Nat.zero_le _ ) hx₁;
             · exact fun x hx₁ hx₂ hx₃ => hx₂ ( hf_mono ( Nat.zero_le _ ) hx₃ );
             · intro x hx₁ hx₂ hx₃; contrapose! hij;
               exact le_antisymm ( le_of_not_gt fun hi => hx₂ <| hf_mono ( by linarith ) hx₃ ) ( le_of_not_gt fun hj => hij <| hf_mono ( by linarith ) hx₁ );
           · intro i; by_cases hi : i = 0 <;> simp +decide [ * ] ;
             convert h_compl _ ( h_disjoint ( fun j => if j = 0 then ( f i ) ᶜ else if j = 1 then f ( i - 1 ) else ∅ ) _ _ ) using 1;
             · ext x; simp +decide [ Set.ext_iff ] ;
               exact ⟨ fun hx n => by rcases n with ( _ | _ | n ) <;> simp +decide [ hx ], fun hx => ⟨ by simpa using hx 0, by simpa using hx 1 ⟩ ⟩;
             · intro j k hjk; rcases j with ( _ | _ | j ) <;> rcases k with ( _ | _ | k ) <;> simp_all +decide [ Set.disjoint_left ] ;
               · exact fun x hx₁ hx₂ => hx₁ ( hf_mono ( Nat.pred_le _ ) hx₂ );
               · exact fun x hx => hf_mono ( Nat.pred_le _ ) hx;
             · intro j; by_cases hj : j = 0 <;> by_cases hj' : j = 1 <;> simp +decide [ * ] ;
               simpa using h_compl _ h_univ;
       · intro hL
         obtain ⟨h_univ, h_compl, h_incr⟩ := hL;
         refine' ⟨ h_univ, _, _ ⟩;
         · intro A hA;
           convert h_compl A hA Set.univ h_univ ( Set.subset_univ A ) using 1 ; simp +decide [ Set.diff_eq ];
         · intro f hf_disjoint hf_mem
           have h_incr_seq : ∀ n, (⋃ i ≤ n, f i) ∈ L := by
             intro n
             induction' n with n ih
             aesop
             generalize_proofs at *;
             have h_union_succ : (⋃ i ≤ n, f i) ∪ f (n + 1) ∈ L := by
               have h_union_succ : (⋃ i ≤ n, f i)ᶜ \ f (n + 1) ∈ L := by
                 apply h_compl;
                 · exact hf_mem _;
                 · convert h_compl _ ih _ h_univ _ using 1 ; aesop;
                   exact Set.subset_univ _;
                 · simp +decide [ Set.subset_def, hf_disjoint ];
                   exact fun x hx i hi => fun hx' => Set.disjoint_left.mp ( hf_disjoint ( by linarith ) ) hx hx';
               convert h_compl _ h_union_succ _ h_univ _ using 1;
               · ext x; by_cases hx : x ∈ ⋃ i ≤ n, f i <;> by_cases hx' : x ∈ f ( n + 1 ) <;> simp +decide [ hx, hx' ] ;
                 · aesop;
                 · exact fun i hi => fun hx'' => hx <| Set.mem_iUnion₂.2 ⟨ i, hi, hx'' ⟩;
               · exact Set.subset_univ _;
             convert h_union_succ using 1;
             exact Set.biUnion_le_succ f n;
           convert h_incr ( fun n => ⋃ i ≤ n, f i ) ( fun n => h_incr_seq n ) ( fun n m hnm => Set.iUnion₂_subset fun i hi => Set.subset_iUnion₂_of_subset i ( le_trans hi hnm ) ( Set.Subset.refl _ ) ) using 1;
           ext x
           simp [Set.mem_iUnion];
           exact ⟨ fun ⟨ i, hi ⟩ => ⟨ i, i, le_rfl, hi ⟩, fun ⟨ i, j, hj, hj' ⟩ => ⟨ j, hj' ⟩ ⟩
