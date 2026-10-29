/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineRowLinearReaders

/-! # Native affine levels and active-height row dispatch -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineRowLevelReader
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineRowLayout FlatAffineRowAccess FlatAffineRowLinearReaders FlatAffineRowPolynomials
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {F : Inputs} {row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)}
  {W : List Bool → ℕ} {target modulus : List Bool → List Bool}

theorem tag_branch (h : F.Access) (hr : UnaryFn (fun u => (row u).val)) (t : ℕ)
    (p q : (u : List Bool) → MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ)
    (hp : SpaceFunction (read F W target modulus p)) (hq : SpaceFunction (read F W target modulus q)) :
    SpaceFunction (read F W target modulus (fun u => if FlatAffineFullSourceTower.tag (levelRecord F row u) = t then p u else q u)) := by
  let flag (u : List Bool) := [decide (FlatAffineFullSourceTower.tag (levelRecord F row u) = t)]
  have Hflag : SpaceFunction flag := (level_evaluator h hr).postcompose
    (fun r => [decide (FlatAffineFullSourceTower.tag r = t)]) (tag_binary.eq (BinaryFn.const t)).flag_mem_FP
  have H := FixedWidthRowBits.select_evaluator (FlatAffineFullSourcePositive.count F) W p q target modulus flag Hflag hp hq
  exact H.congr (funext fun u => by
    unfold FlatAffineRowLinearReaders.read
    simp only [FixedWidthRowBits.value, flag, List.getElem?_cons_zero, Option.getD_some, decide_eq_true_eq])

theorem oldLevel_evaluator (h : F.Access) (hr : UnaryFn (fun u => (row u).val))
    (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (read F W target modulus (oldLevel F row)) := by
  have hc := constant_evaluator h hr hW ht hm
  have hl : SpaceFunction (read F W target modulus (fun u => oldHeight F row u (oldLeft F row u))) :=
    oldHeight_evaluator h hr hW ht hm FlatAffineFullSourceTower.left left_FP
  have hr' : SpaceFunction (read F W target modulus (fun u => oldHeight F row u (oldRight F row u))) :=
    oldHeight_evaluator h hr hW ht hm FlatAffineFullSourceTower.right right_FP
  have hadd := FixedWidthRowBits.add_evaluator (FlatAffineFullSourcePositive.count F) W _ _ target modulus hm hl hr'
  have htwo := tag_branch h hr 2 _ _ hadd hc
  have hone := tag_branch h hr 1 _ _ hl htwo
  exact FixedWidthRowBits.branch_evaluator (FlatAffineFullSourcePositive.count F) W _ _ target modulus
    (fun u => 0 < stage F row u) ((BinaryFn.const 0).lt (BinaryFn.ofUnary (stage_unary h hr))) hone hc

theorem activeFlag_FP : (fun r => [FlatAffineFullSourceTower.active r]) ∈ FP := by
  have H := (FPPred.getBit pairFst_mem_FP (UnaryFn.const 0)).flag_mem_FP
  apply mem_FP_of_eq H
  intro r
  change [decide ((pairFst r)[0]?.getD false = true)] = [(pairFst r).headD false]
  cases pairFst r with
  | nil => rfl
  | cons b bs => cases b <;> rfl

theorem evaluator (h : F.Access) (hr : UnaryFn (fun u => (row u).val))
    (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (read F W target modulus (levelRow F row)) := by
  have hc := currentHeight_evaluator h hr hW ht hm
  have ho := oldLevel_evaluator h hr hW ht hm
  have hd := FixedWidthRowBits.sub_evaluator (FlatAffineFullSourcePositive.count F) W _ _ target modulus hm hc ho
  have hv : UnaryFn (fun u => (multiplier F row u (height F row u).succ).val) :=
    ((offset_unary h hr).add ((FlatAffineFullSourceTower.arity_unary h).add
      ((height_unary h hr).add (UnaryFn.const 1)))).min (FlatAffineFullSourceTower.count_unary h)
  have hx := FixedWidthRowBits.variable_evaluator (FlatAffineFullSourcePositive.count F) W
    (fun u => multiplier F row u (height F row u).succ) target modulus
    (FlatAffineFullSourcePositive.count_unary h) hW hv ht hm
  have hp := (level_evaluator h hr).postcompose (fun r => [FlatAffineFullSourceTower.active r]) activeFlag_FP
  have H := FixedWidthRowBits.select_evaluator (FlatAffineFullSourcePositive.count F) W _ _ target modulus _ hp hd hx
  exact H.congr (funext fun u => by
    unfold FlatAffineRowLinearReaders.read
    simp only [FixedWidthRowBits.value, levelRow, Function.comp_apply, List.getElem?_cons_zero, Option.getD_some])

end LeanCanny.Encoding.FlatAffineRowLevelReader
