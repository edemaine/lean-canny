/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSlopeMaskSpace
/-! # Concrete original-rule recipes need only original level and direction space

The case and coordinate selectors are ordinary original syntax metadata.
No interpreted state, affine coefficient, permutation, or initial-bank
product reader is an input to these constructors.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalScalarRecipe
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Layout (F : Inputs) where
  input : List Bool → List Bool
  height : (u : List Bool) → Fin (arity F u)
  mode : List Bool → ℕ
  row : (q : List Bool) → Fin (arity F (input q))
  sweep : List Bool → Bool

structure Access {F : Inputs} (L : Layout F) : Prop where
  input : L.input ∈ FP
  height : BinaryFn (fun u => (L.height u).val)
  mode : BinaryFn L.mode
  row : BinaryFn (fun q => (L.row q).val)
  sweep : (fun q => [L.sweep q]) ∈ FP

noncomputable def expression {F : Inputs} (L : Layout F) (q : List Bool) : IntegralMixedHistory.AffineExpr :=
  if L.mode q = 1 then FlatAffineExceptionalMixedExpressions.shifted F L.height (L.input q)
    (FlatAffineExceptionalOrderedRule.order F (L.input q) (L.row q))
  else if L.mode q = 2 then FlatAffineExceptionalMixedExpressions.shifted F L.height (L.input q)
    (FlatAffineExceptionalCoarseRule.order F L.height (L.input q) (L.row q))
  else .constant 0

noncomputable def word {F : Inputs} (L : Layout F) (q : List Bool) := IntegralMixedAffineCode.encode (expression L q)

theorem syntax_space {F : Inputs} (hF : F.Access) (L : Layout F) (hL : Access L) : SpaceFunction (word L) := by
  have HO := FlatAffineExceptionalMixedExpressions.shifted_encode_space_source hF L.input hL.input L.height hL.height _
    (FlatAffineExceptionalSelectorSpace.ordered_evaluator hF L.input hL.input L.row hL.row)
  have HC := FlatAffineExceptionalMixedExpressions.shifted_encode_space_source hF L.input hL.input L.height hL.height _
    (FlatAffineExceptionalSelectorSpace.coarse_evaluator hF L.input hL.input L.height hL.height L.row hL.row)
  have H2 := SpaceFunction.branch (fun q => decide (L.mode q = 2)) (hL.mode.eq (BinaryFn.const 2)).flag_mem_FP HC
    (SpaceFunction.ofFP _ (constFn_mem_FP (IntegralMixedAffineCode.encode (.constant 0))))
  have H1 := SpaceFunction.branch (fun q => decide (L.mode q = 1)) (hL.mode.eq (BinaryFn.const 1)).flag_mem_FP HO H2
  apply H1.congr
  funext q
  simp only [word, expression, decide_eq_true_eq]
  split_ifs <;> rfl

noncomputable def slope {F : Inputs} (L : Layout F) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (A : List Bool → ℕ) (q : List Bool) : ℤ :=
  if L.sweep q then
    if A q = ((FlatAffineExceptionalOrderedRule.order F (L.input q)).symm (L.height (L.input q))).val then
      FlatAffineExceptionalBankSource.denominator F C L.height (L.input q) else 0
  else if A q = 0 then 1 else 0

theorem slope_space {F : Inputs} (hF : F.Access) (L : Layout F) (hL : Access L)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (A : List Bool → ℕ) (hA : BinaryFn A)
    (mod : List Bool → List Bool) (hm : mod ∈ FP) :
    SpaceFunction (fun q => residueBits (slope L C A q : ZMod (Nat.fromBitsLE (mod q) + 1))) := by
  have HS := FlatAffineExceptionalSelectorSpace.initial_slope_mask_space hF C L.height hL.height L.input mod hL.input hm A hA
  have H1 : SpaceFunction (fun q => residueBits ((if A q = 0 then 1 else 0 : ℤ) : ZMod (Nat.fromBitsLE (mod q) + 1))) := by
    have HC0 := (hA.eq (BinaryFn.const 0)).ite_mem_FP
      (constFn_mem_FP (SignStatisticBits.integerCode 1)) (constFn_mem_FP (SignStatisticBits.integerCode 0))
    have HC : (fun q => SignStatisticBits.integerCode (if A q = 0 then 1 else 0 : ℤ)) ∈ FP :=
      mem_FP_of_eq HC0 (fun q => by split_ifs <;> rfl)
    have H := SignedIntegerResidue.evaluator (SpaceFunction.ofFP _ HC) hm
    exact H
  have H := SpaceFunction.branch L.sweep hL.sweep HS H1
  apply H.congr
  funext q
  simp only [slope]
  split_ifs <;> rfl
end LeanCanny.Encoding.FlatAffineExceptionalScalarRecipe
