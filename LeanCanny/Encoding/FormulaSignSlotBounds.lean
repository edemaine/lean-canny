/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotSource
/-! # Literal scoping, closedness and native records for sign-slot envelopes -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotSource
open ETR LeanCanny.Computation LeanCanny.Connectivity
open scoped Classical
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension
  ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.query query rawCode raw slotCode dimension count term

theorem weak_scope (q : List Bool) : (weak q).arity≤dimension (pairFst q) := by
  have H := term_scope q
  unfold weak
  split_ifs <;> simp only [Formula.arity,Term.arity] <;> omega

theorem strict_scope (q : List Bool) : (strict q).arity≤dimension (pairFst q) := by
  have H := term_scope q
  unfold strict
  split_ifs <;> simp only [Formula.arity,Term.arity] <;> omega

theorem weak_closed (q : List Bool) : ClosedFormulaWitness.Closed (weak q) := by
  unfold weak
  split_ifs
  · exact .eqZero _
  · exact .nonnegative _
  · exact .nonnegative _
  · exact .falsum

private theorem conjunction_closed (ps : List Formula) (H : ∀ p∈ps, ClosedFormulaWitness.Closed p) :
    ClosedFormulaWitness.Closed (FormulaConjunctionWriter.conjunction ps) := by
  induction ps with
  | nil => exact .verum
  | cons p ps IH =>
    exact .and (H p List.mem_cons_self) (IH (fun q hq => H q (List.mem_cons_of_mem _ hq)))

theorem envelope_closed (c : List Bool) : ClosedFormulaWitness.Closed (envelope c) := by
  unfold envelope
  split_ifs
  · apply conjunction_closed
    simp only [List.forall_mem_map,List.mem_range]
    exact fun i _ => weak_closed _
  · exact .falsum

theorem envelope_scope (c : List Bool) : (envelope c).arity≤dimension c := by
  unfold envelope
  split_ifs
  · apply FormulaConjunctionWriter.arity
    simp only [List.forall_mem_map,List.mem_range]
    intro i _
    simpa only [pairFst_pair] using weak_scope (pair c (List.replicate i true))
  · exact Nat.zero_le _

theorem stratum_scope (c : List Bool) : (stratum c).arity≤dimension c := by
  unfold stratum
  split_ifs
  · apply FormulaConjunctionWriter.arity
    simp only [List.forall_mem_map,List.mem_range]
    intro i _
    simpa only [pairFst_pair] using strict_scope (pair c (List.replicate i true))
  · exact Nat.zero_le _

theorem strict_implies_weak (q : List Bool) (env : ℕ → ℝ) :
    (strict q).Holds env → (weak q).Holds env := by
  unfold strict weak
  split_ifs <;> simp only [Formula.Holds,Term.eval,Int.cast_neg,Int.cast_one] <;> intro H
  · exact H
  · nlinarith
  · nlinarith
  · exact H

theorem stratum_implies_envelope (c : List Bool) (env : ℕ → ℝ) :
    (stratum c).Holds env → (envelope c).Holds env := by
  unfold stratum envelope
  split_ifs
  · simp only [FormulaConjunctionWriter.rangeConjunction,FormulaConjunctionWriter.holds,
      List.forall_mem_map,List.mem_range]
    intro H i hi
    exact strict_implies_weak _ env (H i hi)
  · exact id

noncomputable def description (c : List Bool) : Description := ⟨dimension c,envelope c⟩
noncomputable def strictDescription (c : List Bool) : Description := ⟨dimension c,stratum c⟩

theorem description_wellFormed (c : List Bool) : (description c).WellFormed := envelope_scope c
theorem strictDescription_wellFormed (c : List Bool) : (strictDescription c).WellFormed := stratum_scope c

theorem whole_record_FP : (fun c => (Input.whole (description c)).encode) ∈ FP := by
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 1 (Codec.unary_toBits_mem_FP dimension_unary) envelope_FP)
  intro c
  simp only [Codec.taggedTwo_toBits,Input.encode,Input.toData,description,Formula.encode]

theorem strict_record_FP : (fun c => (Input.whole (strictDescription c)).encode) ∈ FP := by
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 1 (Codec.unary_toBits_mem_FP dimension_unary) stratum_FP)
  intro c
  simp only [Codec.taggedTwo_toBits,Input.encode,Input.toData,strictDescription,Formula.encode]

end LeanCanny.Encoding.FormulaSignSlotSource
