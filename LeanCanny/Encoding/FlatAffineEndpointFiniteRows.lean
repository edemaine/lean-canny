/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteFrame
public import LeanCanny.Encoding.FrozenSquareRows

/-! # Original-source row readers for the joint finite midpoint frame

Both retained height equations and every embedded original row are read
internally. Arbitrary query contexts retain their width and modulus fields;
no expanded algebraic coefficients are supplied.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteRows
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def inner (F : Inputs) (height : (u : List Bool) → Fin (count F u)) : SquareIntegerRows.Family where
  count := FlatAffineEndpointRows.arity F
  count_pos _ := Nat.zero_lt_succ _
  system := FlatAffineEndpointPreparation.system F height

noncomputable def innerSelected (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (q : List Bool) :
    Fin (FlatAffineEndpointRows.arity F (SquareSampleInput.source q)) :=
  SquareIntegerRows.selected (inner F height) (SquareSampleInput.source q) (SquareSampleInput.indexWord q)

theorem innerSelected_unary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) :
    UnaryFn (fun q => (innerSelected F height q).val) :=
  UnaryFn.fromBitsLE_min SquareSampleInput.indexWord_FP
    (((FlatAffineEndpointRows.arity_unary h).comp SquareSampleInput.source_FP).sub (UnaryFn.const 1))

theorem innerAccess {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : (inner F height).Access := by
  refine ⟨FlatAffineEndpointRows.arity_unary h, ?_⟩
  have E := FlatAffineEndpointCoefficient.rowEvaluator h height hh SquareSampleInput.source SquareSampleInput.source_FP
    (innerSelected F height) (innerSelected_unary h height) (UnaryFn.length SquareSampleInput.widthWord_FP)
    SquareSampleInput.rankWord_FP SquareSampleInput.modulusWord_FP
  exact E.congr (funext fun _ => rfl)

theorem retainedEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (PrimitivePairBits.coefficient (FlatAffineEndpointFiniteFrame.retained F height)) :=
  IntegerPolynomialStationaryBits.evaluator _ (FlatAffineEndpointExceptional.evaluator h height hh)

theorem rowEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (ctx : List Bool → List Bool) (hctx : ctx ∈ FP)
    (row : (q : List Bool) → Fin (FlatAffineEndpointFiniteFrame.arity F (ctx q)))
    (hr : UnaryFn (fun q => (row q).val)) {W : List Bool → ℕ} (hW : UnaryFn W)
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (FlatAffineEndpointFiniteFrame.arity F ∘ ctx) W
      (fun q => FlatAffineEndpointFiniteFrame.system F height (ctx q) (row q)) target modulus) := by
  let rctx := pairFst ∘ ctx
  have hrc : rctx ∈ FP := mem_FP_comp hctx pairFst_mem_FP
  have A := SquareIntegerRows.access_comp (innerAccess h height hh) hrc
  have EP := PolynomialFamilyProductBits.reindexEvaluator (retainedEvaluator h height hh) rctx hrc
  have E := FrozenSquareRows.evaluator A (fun q => FlatAffineEndpointGram.active F height (rctx q))
    ((FlatAffineEndpointGram.active_unary height hh).comp hrc) row hr hW
    (FlatAffineEndpointFiniteFrame.retained F height ∘ rctx) EP ht hm
  exact E.congr (funext fun _ => rfl)

noncomputable def family (F : Inputs) (height : (u : List Bool) → Fin (count F u)) : SquareIntegerRows.Family where
  count := FlatAffineEndpointFiniteFrame.arity F
  count_pos _ := Nat.zero_lt_succ _
  system := FlatAffineEndpointFiniteFrame.system F height

noncomputable def selected (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (q : List Bool) :
    Fin (FlatAffineEndpointFiniteFrame.arity F (SquareSampleInput.source q)) :=
  SquareIntegerRows.selected (family F height) (SquareSampleInput.source q) (SquareSampleInput.indexWord q)

theorem selected_unary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) :
    UnaryFn (fun q => (selected F height q).val) :=
  UnaryFn.fromBitsLE_min SquareSampleInput.indexWord_FP
    (((FlatAffineEndpointFiniteFrame.arity_unary h).comp SquareSampleInput.source_FP).sub (UnaryFn.const 1))

theorem access {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : (family F height).Access := by
  refine ⟨FlatAffineEndpointFiniteFrame.arity_unary h, ?_⟩
  have E := rowEvaluator h height hh SquareSampleInput.source SquareSampleInput.source_FP
    (selected F height) (selected_unary h height) (UnaryFn.length SquareSampleInput.widthWord_FP)
    SquareSampleInput.rankWord_FP SquareSampleInput.modulusWord_FP
  exact E.congr (funext fun _ => rfl)

end LeanCanny.Encoding.FlatAffineEndpointFiniteRows
