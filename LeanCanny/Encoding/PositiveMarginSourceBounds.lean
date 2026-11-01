/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.PositiveMarginSource
public import LeanCanny.Connectivity.InputFP
/-! # Literal scopes and native canonical records for the positive-margin source -/
@[expose] public section
namespace LeanCanny.Encoding.PositiveMarginSource
open LeanCanny.Computation ETR LeanCanny.Geometry LeanCanny.Connectivity
open MonotoneGateSource WeakCircleCanonicalFormula
open scoped Classical

theorem operand_arity (F : Family) (side : Bool) (q : List Bool) :
    (operand F side q).arity≤valueIndex F q := by
  cases side <;> dsimp only [operand,Bool.false_eq_true,ite_false,ite_true] <;>
    split_ifs <;> simp only [Term.arity,valueIndex] <;> omega

theorem body_arity (F : Family) (q : List Bool) : (body F q).arity≤valueIndex F q := by
  have HL:=operand_arity F false q
  have HR:=operand_arity F true q
  unfold body
  split_ifs <;> simp only [Term.arity] <;> omega

theorem condition_arity (F : Family) (q : List Bool)
    (ha : (F.atom q).arity≤dimension F q) : (condition F q).arity≤valueIndex F q+1 := by
  have HB:=body_arity F q
  unfold condition
  split_ifs
  · rw [PositivePartGraph.arity]
    dsimp [valueIndex]
    omega
  · simp only [Formula.arity,difference,Term.arity]
    omega

theorem root_arity (F : Family) (c : List Bool) : (root F c).arity≤F.dimension c+F.count c := by
  unfold root
  split_ifs <;> simp only [Term.arity] <;> omega

theorem reciprocal_arity (F : Family) (c : List Bool) : (reciprocal F c).arity≤total F c := by
  have HR:=root_arity F c
  simp only [reciprocal,difference,Term.arity,total]
  omega

theorem source_arity (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (source F c).arity≤total F c := by
  apply max_le (reciprocal_arity F c)
  apply FormulaConjunctionWriter.arity
  simp only [List.forall_mem_map,List.mem_range]
  intro i hi
  have HA:=condition_arity F (pair c (List.replicate i true))
    (by simpa only [dimension,pairFst_pair] using ha i hi)
  simp only [valueIndex,dimension,index,pairFst_pair,pairSnd_pair,List.length_replicate] at HA
  dsimp [total]
  omega

def description (F : Family) (c : List Bool) : Description := ⟨total F c,source F c⟩

theorem description_wellFormed (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (description F c).WellFormed := source_arity F c ha

theorem total_unary (F : Family) (hF : Access F) : UnaryFn (total F) := (hF.dimension.add hF.count).add (UnaryFn.const 1)

theorem whole_record_FP (F : Family) (hF : Access F) :
    (fun c => (Input.whole (description F c)).encode) ∈ FP := by
  have H:=Codec.taggedTwo_mem_FP 1 (Codec.unary_toBits_mem_FP (total_unary F hF)) (source_FP F hF)
  exact mem_FP_of_eq H (fun _ => Codec.taggedTwo_toBits 1 _ _)

end LeanCanny.Encoding.PositiveMarginSource
