/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotMarginSource
/-! # The actual selected strict stratum is one positive-margin region of its weak envelope -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotMargin
open ETR LeanCanny.Computation LeanCanny.Connectivity FormulaSignSlotSource
open scoped Classical
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count
  FormulaSignSlotSource.count FormulaSignSlotSource.dimension slotCode term

theorem factor_nonneg (q : List Bool) (env : ℕ → ℝ) (H : (weak q).Holds env) : 0≤(factor q).eval env := by
  simp only [weak,factor] at H ⊢
  split_ifs at H ⊢ <;> simp only [Formula.Holds,Term.eval,Int.cast_neg,Int.cast_one] at H ⊢
  · exact zero_le_one
  · linarith
  · exact le_of_not_gt H

theorem factor_pos_iff (q : List Bool) (env : ℕ → ℝ) (H : (weak q).Holds env) :
    0 < (factor q).eval env ↔ (strict q).Holds env := by
  simp only [weak,factor,strict] at H ⊢
  split_ifs at H ⊢ <;> simp only [Formula.Holds,Term.eval,Int.cast_neg,Int.cast_one] at H ⊢
  · exact ⟨fun _ => H,fun _ => zero_lt_one⟩
  · constructor <;> intro h <;> linarith
  · constructor <;> intro h <;> linarith

private theorem prod_pos_iff (xs : List ℝ) (HN : ∀ x∈xs,0≤x) :
    0 < xs.prod ↔ ∀ x∈xs,0 < x := by
  induction xs with
  | nil => simp
  | cons x xs IH =>
    have HX := HN x List.mem_cons_self
    have HT := IH (fun y hy => HN y (List.mem_cons_of_mem _ hy))
    rw [List.prod_cons,List.forall_mem_cons]
    constructor
    · intro H
      rcases mul_pos_iff.mp H with H | H
      · exact ⟨H.1,HT.mp H.2⟩
      · exact ((not_lt_of_ge HX) H.1).elim
    · rintro ⟨H1,H2⟩
      exact mul_pos H1 (HT.mpr H2)

theorem margin_nonneg (c : List Bool) (env : ℕ → ℝ) (H : (envelope c).Holds env) :
    0≤(margin c).eval env := by
  unfold envelope at H
  split_ifs at H
  · have HW : ∀ i < count c, (weak (pair c (List.replicate i true))).Holds env := by
      simpa only [FormulaConjunctionWriter.rangeConjunction,FormulaConjunctionWriter.holds,
        List.forall_mem_map,List.mem_range] using H
    rw [margin,TermProduct.eval_accumulate]
    simp only [Term.eval,Int.cast_one,one_mul]
    apply List.prod_nonneg
    simp only [factors,List.forall_mem_map,List.mem_range]
    exact fun i hi => factor_nonneg _ env (HW i hi)
  · exact H.elim

theorem margin_positive_iff (c : List Bool) (env : ℕ → ℝ) (H : (envelope c).Holds env) :
    0 < (margin c).eval env ↔ (stratum c).Holds env := by
  unfold envelope at H
  split_ifs at H with HL
  · have HW : ∀ i < count c, (weak (pair c (List.replicate i true))).Holds env := by
      simpa only [FormulaConjunctionWriter.rangeConjunction,FormulaConjunctionWriter.holds,
        List.forall_mem_map,List.mem_range] using H
    have HN : ∀ x∈(factors c).map (fun f => f.eval env),0≤x := by
      simp only [factors,List.forall_mem_map,List.mem_range]
      exact fun i hi => factor_nonneg _ env (HW i hi)
    rw [margin,TermProduct.eval_accumulate]
    simp only [Term.eval,Int.cast_one,one_mul]
    rw [prod_pos_iff _ HN]
    rw [stratum,ite_eq_left HL,FormulaConjunctionWriter.rangeConjunction,FormulaConjunctionWriter.holds]
    simp only [factors,List.forall_mem_map,List.mem_range]
    apply forall₂_congr
    intro i hi
    exact factor_pos_iff _ env (HW i hi)
  · exact H.elim

end LeanCanny.Encoding.FormulaSignSlotMargin
