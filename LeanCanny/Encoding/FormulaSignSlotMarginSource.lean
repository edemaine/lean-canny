/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotSemantics
public import LeanCanny.ETR.TermProductFP
public import LeanCanny.ETR.PolynomialMass
/-! # A native polynomial margin for each selected original sign stratum -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotMargin
open ETR LeanCanny.Computation LeanCanny.Connectivity FormulaSignSlotSource
open scoped Classical

noncomputable def factor (q : List Bool) : Term :=
  if slotCode q=[false,false] then .const 1 else
  if slotCode q=[false,true] then .mul (.const (-1)) (term q) else
  if slotCode q=[true,false] then term q else .const 0
noncomputable def factors (c : List Bool) : List Term :=
  (List.range (count c)).map (fun i => factor (pair c (List.replicate i true)))
noncomputable def margin (c : List Bool) : Term := TermProduct.accumulate (factors c) (.const 1)

attribute [local irreducible] pair Input.field slotCode term count dimension

private theorem iteTerm_FP {P : List Bool → Prop} [DecidablePred P] (hP : FPPred P)
    {a b : List Bool → Term} (ha : (fun q => (a q).toData.toBits) ∈ FP)
    (hb : (fun q => (b q).toData.toBits) ∈ FP) :
    (fun q => (if P q then a q else b q).toData.toBits) ∈ FP := by
  apply mem_FP_of_eq (hP.ite_mem_FP ha hb)
  intro q
  split_ifs <;> rfl

theorem factor_FP : (fun q => (factor q).toData.toBits) ∈ FP := by
  have HN : (fun q => (Term.mul (.const (-1)) (term q)).toData.toBits) ∈ FP :=
    mem_FP_of_eq (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (Term.const (-1)).toData.toBits) term_FP)
      (fun _ => (Term.mul_toBits _ _).symm)
  unfold factor
  exact iteTerm_FP (Brackets.stringEq_fppred slotCode_FP (constFn_mem_FP [false,false])) (constFn_mem_FP (Term.const 1).toData.toBits)
    (iteTerm_FP (Brackets.stringEq_fppred slotCode_FP (constFn_mem_FP [false,true])) HN
      (iteTerm_FP (Brackets.stringEq_fppred slotCode_FP (constFn_mem_FP [true,false])) term_FP
        (constFn_mem_FP (Term.const 0).toData.toBits)))

theorem factorsBits_FP : (fun c => SumSquares.listBits (factors c)) ∈ FP := by
  have H := flatMap_range_mem_FP factor_FP count_unary.mem_FP
  have HR : (fun c => (List.range (count c)).flatMap (fun i =>
      (factor (pair c (List.replicate i true))).toData.toBits)) ∈ FP := by
    simpa only [List.length_replicate] using H
  apply mem_FP_of_eq (mem_FP_comp HR Brackets.wrap_mem_FP)
  intro c
  simp only [Function.comp_apply,factors,SumSquares.listBits,Data.toBits_l,List.map_map,
    List.flatten_eq_flatMap,List.flatMap_map,Function.comp_def,id_eq,Brackets.wrap]

theorem margin_FP : (fun c => (margin c).toData.toBits) ∈ FP := by
  apply mem_FP_of_eq (mem_FP_comp factorsBits_FP TermProduct.collapse_mem_FP)
  intro c
  rw [Function.comp_apply,TermProduct.collapse_listBits]
  rfl

noncomputable def budget (c : List Bool) := (margin c).toData.size

theorem budget_unary : UnaryFn budget :=
  (UnaryFn.length margin_FP).of_eq (fun c => Data.length_toBits (margin c).toData)

theorem factor_scope (q : List Bool) : (factor q).arity≤dimension (pairFst q) := by
  have HT := term_scope q
  unfold factor
  split_ifs
  · exact Nat.zero_le _
  · simpa only [Term.arity,Nat.zero_max] using HT
  · exact HT
  · exact Nat.zero_le _

theorem margin_scope (c : List Bool) : (margin c).arity≤dimension c := by
  apply TermProduct.arity_accumulate_le _ _ _ (Nat.zero_le _)
  simp only [factors,List.forall_mem_map,List.mem_range]
  intro i _
  simpa only [pairFst_pair] using factor_scope (pair c (List.replicate i true))

theorem margin_degree (c : List Bool) (n : ℕ) : ((margin c).finitePolynomial n).totalDegree≤budget c :=
  (Term.totalDegree_finitePolynomial _ _).trans (Term.degreeBound_le_dataSize _)

theorem margin_mass (c : List Bool) (n : ℕ) :
    LeanCanny.Algebra.MvMass.mass ((margin c).finitePolynomial n)≤2^budget c := Term.finitePolynomial_mass _ _

end LeanCanny.Encoding.FormulaSignSlotMargin
