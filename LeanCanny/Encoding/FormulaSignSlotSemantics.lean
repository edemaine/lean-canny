/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotCircuit
/-! # Exact signs and literal arithmetic terms of original atomic slots -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotSource
open ETR LeanCanny.Computation LeanCanny.Connectivity
open scoped Classical
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count

theorem signCode_injective : Function.Injective signCode := by
  intro a b H
  cases a <;> cases b <;> simp_all [signCode]

theorem strict_sign_iff (q : List Bool) (env : ℕ → ℝ) :
    (strict q).Holds env ↔ slotCode q=signCode (SignType.sign ((term q).eval env)) := by
  constructor
  · intro H
    unfold strict at H
    split_ifs at H with H0 H1 H2
    · rw [sign_eq_zero_iff.mpr H]
      exact H0
    · rw [sign_neg H]
      exact H1
    · have HE : 0 < (term q).eval env := by
        simp only [Formula.Holds,Term.eval,Int.cast_neg,Int.cast_one] at H
        change (-1 : ℝ)*(term q).eval env < 0 at H
        nlinarith
      rw [sign_pos HE]
      exact H2
    · exact H.elim
  · intro H
    exact strict_of_code q env _ H rfl

theorem stratum_slot (c : List Bool) (env : ℕ → ℝ) (H : (stratum c).Holds env)
    (i : ℕ) (hi : i < count c) : (strict (pair c (List.replicate i true))).Holds env := by
  unfold stratum at H
  split_ifs at H
  · exact (FormulaConjunctionWriter.holds _ _).mp H _
      (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)
  · exact H.elim

theorem query_pair (c label : List Bool) (i : ℕ) :
    query (pair (pair c label) (List.replicate i true))=pair (Input.field 2 c) (BinaryNatCode.encode i) := by
  simp only [query,ClosedFormulaGateMetadata.query,MonotoneGateSource.index,
    pairFst_pair,pairSnd_pair,List.length_replicate]

theorem term_of_raw (q : List Bool) (H : (raw q).arity≤dimension (pairFst q)) : term q=raw q := by
  unfold term termCode
  rw [ite_eq_left H,TermView.normalize_eq_term,TermView.term_toBits]
  rfl

theorem eq_atomic_term (q : List Bool) (t : Term)
    (hn : FormulaBooleanCircuitSource.node (query q)=(Formula.eqZero t).encode)
    (ht : t.arity≤dimension (pairFst q)) : term q=t := by
  have HE : raw q=t := FormulaBooleanCircuitSource.term_eq_node (query q) t hn
  rw [term_of_raw q (by rw [HE]; exact ht),HE]

theorem lt_atomic_term (q : List Bool) (t : Term)
    (hn : FormulaBooleanCircuitSource.node (query q)=(Formula.ltZero t).encode)
    (ht : t.arity≤dimension (pairFst q)) : term q=t := by
  have HE : raw q=t := FormulaBooleanCircuitSource.term_lt_node (query q) t hn
  rw [term_of_raw q (by rw [HE]; exact ht),HE]

end LeanCanny.Encoding.FormulaSignSlotSource
