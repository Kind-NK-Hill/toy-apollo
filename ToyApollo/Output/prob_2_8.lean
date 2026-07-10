/-
TASK ID: prob_2_8
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.def_2_7
import ToyApollo.Output.thm_2_6

open Set

inductive Ω₆ where | a | b | c | d | e | f
  deriving DecidableEq, Fintype

open Ω₆

private abbrev m_gen : MeasurableSpace Ω₆ :=
  MeasurableSpace.generateFrom {({a, c, d} : Set Ω₆), {c, d, f}}

private noncomputable def m_partition : MeasurableSpace Ω₆ where
  MeasurableSet' s := (c ∈ s ↔ d ∈ s) ∧ (b ∈ s ↔ e ∈ s)
  measurableSet_empty := by simp
  measurableSet_compl := by
    intro s ⟨h1, h2⟩
    exact ⟨by simp [mem_compl_iff]; tauto, by simp [mem_compl_iff]; tauto⟩
  measurableSet_iUnion := by
    intro f hf
    simp only [mem_iUnion]
    exact ⟨⟨fun ⟨i, hi⟩ => ⟨i, (hf i).1.mp hi⟩, fun ⟨i, hi⟩ => ⟨i, (hf i).1.mpr hi⟩⟩,
           ⟨fun ⟨i, hi⟩ => ⟨i, (hf i).2.mp hi⟩, fun ⟨i, hi⟩ => ⟨i, (hf i).2.mpr hi⟩⟩⟩

private lemma atom_a_measurable : @MeasurableSet Ω₆ m_gen {a} := by
  have h1 : @MeasurableSet Ω₆ m_gen {a, c, d} :=
    MeasurableSpace.measurableSet_generateFrom (by simp)
  have h2 : @MeasurableSet Ω₆ m_gen {c, d, f} :=
    MeasurableSpace.measurableSet_generateFrom (by simp)
  have h3 : ({a} : Set Ω₆) = {a, c, d} ∩ {c, d, f}ᶜ := by ext x; fin_cases x <;> simp
  rw [h3]; exact h1.inter h2.compl

private lemma atom_cd_measurable : @MeasurableSet Ω₆ m_gen {c, d} := by
  have h1 : @MeasurableSet Ω₆ m_gen {a, c, d} :=
    MeasurableSpace.measurableSet_generateFrom (by simp)
  have h2 : @MeasurableSet Ω₆ m_gen {c, d, f} :=
    MeasurableSpace.measurableSet_generateFrom (by simp)
  have h3 : ({c, d} : Set Ω₆) = {a, c, d} ∩ {c, d, f} := by ext x; fin_cases x <;> simp
  rw [h3]; exact h1.inter h2

private lemma atom_f_measurable : @MeasurableSet Ω₆ m_gen {f} := by
  have h1 : @MeasurableSet Ω₆ m_gen {a, c, d} :=
    MeasurableSpace.measurableSet_generateFrom (by simp)
  have h2 : @MeasurableSet Ω₆ m_gen {c, d, f} :=
    MeasurableSpace.measurableSet_generateFrom (by simp)
  have h3 : ({f} : Set Ω₆) = {c, d, f} ∩ {a, c, d}ᶜ := by ext x; fin_cases x <;> simp
  rw [h3]; exact h2.inter h1.compl

private lemma atom_be_measurable : @MeasurableSet Ω₆ m_gen {b, e} := by
  have h1 : @MeasurableSet Ω₆ m_gen {a, c, d} :=
    MeasurableSpace.measurableSet_generateFrom (by simp)
  have h2 : @MeasurableSet Ω₆ m_gen {c, d, f} :=
    MeasurableSpace.measurableSet_generateFrom (by simp)
  have h3 : ({b, e} : Set Ω₆) = ({a, c, d} ∪ {c, d, f})ᶜ := by ext x; fin_cases x <;> simp
  rw [h3]; exact (h1.union h2).compl

open Classical in

private lemma decompose_partition (s : Set Ω₆) (hcd : c ∈ s ↔ d ∈ s) (hbe : b ∈ s ↔ e ∈ s) :
    s = (if a ∈ s then {a} else ∅) ∪ (if c ∈ s then {c, d} else ∅) ∪
        (if f ∈ s then {f} else ∅) ∪ (if b ∈ s then {b, e} else ∅) := by
          ext x; fin_cases x <;> aesop;

open Classical in

private lemma m_partition_le_m_gen : m_partition ≤ m_gen := by
  intro s ⟨hcd, hbe⟩
  rw [decompose_partition s hcd hbe]
  apply MeasurableSet.union
  apply MeasurableSet.union
  apply MeasurableSet.union
  all_goals (split_ifs <;> first | exact atom_a_measurable | exact atom_cd_measurable | exact atom_f_measurable | exact atom_be_measurable | exact @MeasurableSet.empty _ m_gen)

private lemma m_gen_le_m_partition : m_gen ≤ m_partition := by
  apply MeasurableSpace.generateFrom_le
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl <;> exact ⟨by decide, by decide⟩

private lemma m_gen_eq_m_partition : m_gen = m_partition :=
  le_antisymm m_gen_le_m_partition m_partition_le_m_gen

private lemma m_partition_sets_eq :
    {s : Set Ω₆ | @MeasurableSet _ m_partition s} =
      {∅, {c, d}, {a}, {f}, {b, e}, {a, c, d}, {c, d, f}, {c, d, b, e}, {a, f}, {a, b, e},
       {f, b, e}, {a, c, d, f}, {a, b, c, d, e}, {c, d, f, b, e}, {a, f, b, e}, Set.univ} := by
         ext s
         constructor;
         · intro hs;
           have h_cases : (c ∈ s ↔ d ∈ s) ∧ (b ∈ s ↔ e ∈ s) := by
              change (c ∈ s ↔ d ∈ s) ∧ (b ∈ s ↔ e ∈ s) at hs
              exact hs
           by_cases ha : a ∈ s <;> by_cases hf : f ∈ s <;> simp_all +decide [ Set.ext_iff ];
           · by_cases hb : b ∈ s <;> by_cases he : e ∈ s <;> simp_all +decide [ Set.ext_iff ];
             · by_cases hc : c ∈ s <;> by_cases hd : d ∈ s <;> simp_all +decide [ Set.ext_iff ];
               · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| fun x => by fin_cases x <;> tauto;
               · right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; intro x; fin_cases x <;> simp +decide [ * ] ;
             · by_cases hc : c ∈ s <;> by_cases hd : d ∈ s <;> simp_all +decide [ Set.ext_iff ];
               · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| fun x => by fin_cases x <;> simp +decide [ * ] ;
               · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| fun x => by fin_cases x <;> simp +decide [ * ] ;
           · by_cases hc : c ∈ s <;> by_cases hb : b ∈ s <;> simp_all +decide [ Set.ext_iff ];
             · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| by intro x; fin_cases x <;> simp +decide [ * ] ;
             · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| by intro x; fin_cases x <;> simp +decide [ * ] ;
             · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| fun x => by fin_cases x <;> simp +decide [ * ] ;
             · exact Or.inr <| Or.inr <| Or.inl <| fun x => by fin_cases x <;> tauto;
           · by_cases hc : c ∈ s <;> by_cases hb : b ∈ s <;> simp_all +decide [ Fin.forall_fin_succ ];
             · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| by intro x; fin_cases x <;> simp +decide [ * ] ;
             · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| by intro x; fin_cases x <;> simp +decide [ * ] ;
             · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| by intro x; fin_cases x <;> simp +decide [ * ] ;
             · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| fun x => by fin_cases x <;> tauto;
           · by_cases hb : b ∈ s <;> by_cases hc : c ∈ s <;> simp_all +decide [ Set.ext_iff ];
             · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| by intro x; fin_cases x <;> simp +decide [ * ] ;
             · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| fun x => by fin_cases x <;> simp +decide [ * ] ;
             · exact Or.inr <| Or.inl <| fun x => by fin_cases x <;> simp +decide [ * ] ;
             · exact Or.inl fun x => by fin_cases x <;> tauto;
         · rintro ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) <;> simp +decide [*];
           all_goals constructor;
           all_goals simp +decide ;

theorem prob_2_8 :
    let Ω := Ω₆
    let A₁ : Set Ω := {a, c, d}
    let A₂ : Set Ω := {c, d, f}
    {s : Set Ω | @MeasurableSet Ω (MeasurableSpace.generateFrom {A₁, A₂}) s} =
      {∅, {c, d}, {a}, {f}, {b, e}, {a, c, d}, {c, d, f}, {c, d, b, e}, {a, f}, {a, b, e}, {f, b, e},
       {a, c, d, f}, {a, b, c, d, e}, {c, d, f, b, e}, {a, f, b, e}, Set.univ} := by
  simp only
  change {s : Set Ω₆ | @MeasurableSet _ m_gen s} = _
  rw [m_gen_eq_m_partition]
  exact m_partition_sets_eq
