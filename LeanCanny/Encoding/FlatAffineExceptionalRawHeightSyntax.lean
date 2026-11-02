/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalHeightSyntaxFP
/-! # Total bounded syntax kernel for an original affine height record -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalMixedExpressions
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open FlatAffineFullSourceTower (Inputs arity stageWidth)
set_option backward.isDefEq.respectTransparency false

def rawHeight (F : Inputs) (u : List Bool) (t : ℕ) (v : List Bool) : AffineExpr :=
  sum (List.ofFn (fun i : Fin (arity F u) => .scale
    (FlatAffineFullSourceTower.integer (F.width u) v i.val) (.reference (i.val + stageWidth F u * t + 1))))

theorem rawHeight_eq (F : Inputs) (u : List Bool) (t : Fin (F.depth u)) (v : List Bool) :
    rawHeight F u t.val v = height F u t (fun i => FlatAffineFullSourceTower.integer (F.width u) v i.val) := by
  rfl

theorem rawHeight_encode_FP {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP)
    (T : List Bool → ℕ) (ht : UnaryFn T) (V : List Bool → List Bool) (hv : V ∈ FP) :
    (fun q => IntegralMixedAffineCode.encode (rawHeight F (input q) (T q) (V q))) ∈ FP := by
  let N := fun q => arity F (input q)
  let e := fun q (i : Fin (N q)) => AffineExpr.scale
    (FlatAffineFullSourceTower.integer (F.width (input q)) (V q) i.val)
    (.reference (i.val + stageWidth F (input q) * T q + 1))
  let W := fun p => F.width (input (pairFst p))
  let I := fun p : List Bool => (pairSnd p).length
  let R := fun p => I p + stageWidth F (input (pairFst p)) * T (pairFst p) + 1
  let E := fun p => IntegralMixedAffineCode.encode (.scale
    (FlatAffineFullSourceTower.integer (W p) (V (pairFst p)) (I p)) (.reference (R p)))
  have HN : UnaryFn N := (FlatAffineFullSourceTower.arity_unary hF).comp hi
  have HW : UnaryFn W := hF.width.comp (mem_FP_comp pairFst_mem_FP hi)
  have HI : UnaryFn I := UnaryFn.length pairSnd_mem_FP
  have HB := (FlatAffineFullSourceTower.stageWidth_unary hF).comp (mem_FP_comp pairFst_mem_FP hi)
  have HR : UnaryFn R := (HI.add (HB.mul (ht.comp pairFst_mem_FP))).add (UnaryFn.const 1)
  have HE : E ∈ FP := IntegralMixedAffineCode.scaledReference_FP W I R (fun p => V (pairFst p)) HW HI HR (mem_FP_comp pairFst_mem_FP hv)
  have H := IntegralMixedAffineCode.sumCode_FP N E HN HE
  apply mem_FP_of_eq H
  intro q
  apply IntegralMixedAffineCode.sumCode_eq N e E
  intro c j hj
  simp only [E, e, W, I, R, pairFst_pair, pairSnd_pair, List.length_replicate]
end LeanCanny.Encoding.FlatAffineExceptionalMixedExpressions
