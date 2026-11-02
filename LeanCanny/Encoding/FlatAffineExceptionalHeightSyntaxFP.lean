/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedAffineLiteralFP
/-! # Actual exceptional height syntax has a native writer -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalMixedExpressions
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open FlatAffineExceptionalBankSource (births)
set_option backward.isDefEq.respectTransparency false

theorem spatialIndex_val (F : Inputs) (u : List Bool) (t : Fin (F.depth u)) (i : Fin (arity F u)) :
    (FlatAffineExceptionalParentBank.spatialIndex F u t i).val = i.val + stageWidth F u * t.val + 1 := rfl

theorem height_encode_FP {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP)
    (T : (q : List Bool) → Fin (F.depth (input q))) (ht : UnaryFn (fun q => (T q).val))
    (V : List Bool → List Bool) (hv : V ∈ FP) :
    (fun q => IntegralMixedAffineCode.encode (height F (input q) (T q)
      (fun i => FlatAffineFullSourceTower.integer (F.width (input q)) (V q) i.val))) ∈ FP := by
  let N := fun q => arity F (input q)
  let e := fun q (i : Fin (N q)) => IntegralMixedHistory.AffineExpr.scale
    (FlatAffineFullSourceTower.integer (F.width (input q)) (V q) i.val)
    (.reference (FlatAffineExceptionalParentBank.spatialIndex F (input q) (T q) i).val)
  let W := fun p => F.width (input (pairFst p))
  let I := fun p : List Bool => (pairSnd p).length
  let R := fun p => I p + stageWidth F (input (pairFst p)) * (T (pairFst p)).val + 1
  let E := fun p => IntegralMixedAffineCode.encode (.scale
    (FlatAffineFullSourceTower.integer (W p) (V (pairFst p)) (I p)) (.reference (R p)))
  have HN : UnaryFn N := (FlatAffineFullSourceTower.arity_unary hF).comp hi
  have HW : UnaryFn W := hF.width.comp (mem_FP_comp pairFst_mem_FP hi)
  have HI : UnaryFn I := UnaryFn.length pairSnd_mem_FP
  have HB := (FlatAffineFullSourceTower.stageWidth_unary hF).comp (mem_FP_comp pairFst_mem_FP hi)
  have HR : UnaryFn R := ((HI.add (HB.mul (ht.comp pairFst_mem_FP))).add (UnaryFn.const 1))
  have HE : E ∈ FP := IntegralMixedAffineCode.scaledReference_FP W I R (fun p => V (pairFst p)) HW HI HR (mem_FP_comp pairFst_mem_FP hv)
  have H := IntegralMixedAffineCode.sumCode_FP N E HN HE
  apply mem_FP_of_eq H
  intro q
  apply IntegralMixedAffineCode.sumCode_eq N e E
  intro c j hj
  have HT : (T (pairFst (pair c (List.replicate j true)))).val = (T c).val :=
    congrArg (fun z => (T z).val) (pairFst_pair _ _)
  simp only [E, e, W, I, R, pairFst_pair, pairSnd_pair, List.length_replicate, spatialIndex_val]
  rw [HT]

theorem height_encode_space {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP)
    (T : (q : List Bool) → Fin (F.depth (input q))) (ht : UnaryFn (fun q => (T q).val))
    (V : List Bool → List Bool) (hv : SpaceFunction V) :
    SpaceFunction (fun q => IntegralMixedAffineCode.encode (height F (input q) (T q)
      (fun i => FlatAffineFullSourceTower.integer (F.width (input q)) (V q) i.val))) := by
  have H := height_encode_FP hF (fun p => input (pairFst p)) (mem_FP_comp pairFst_mem_FP hi)
    (fun p => T (pairFst p)) (ht.comp pairFst_mem_FP) pairSnd pairSnd_mem_FP
  apply (hv.withInput.postcompose _ H).congr
  funext q
  exact congrArg₂ (fun (c : List Bool) (v : List Bool) => IntegralMixedAffineCode.encode
    (height F (input c) (T c) (fun i => FlatAffineFullSourceTower.integer (F.width (input c)) v i.val)))
    (pairFst_pair _ _) (pairSnd_pair _ _)
end LeanCanny.Encoding.FlatAffineExceptionalMixedExpressions
