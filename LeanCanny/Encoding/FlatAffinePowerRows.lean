/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerDegree
public import LeanCanny.Encoding.FlatAffineFullSourceContext
public import LeanCanny.Algebra.HomogenizationPolynomialSpace

/-! # Native mixed-degree homogenization of actual affine power rows -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerPositive
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatAffineFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

lemma rawSystem_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) :
    rawSystem (FlatAffineFullSourceContext.comp F f) u = rawSystem F (f u) := by
  have hs : (fun t : Fin (F.depth (f u)) => FlatAffineFullSourceTower.free (FlatAffineFullSourceContext.comp F f) u t.val) =
      fun t : Fin (F.depth (f u)) => FlatAffineFullSourceTower.free F (f u) t.val :=
    funext (fun t => FlatAffineFullSourceContext.free_comp F f u t.val)
  have ha : (fun t : Fin (F.depth (f u)) => FlatAffineFullSourceTower.direction (FlatAffineFullSourceContext.comp F f) u t.val) =
      fun t : Fin (F.depth (f u)) => FlatAffineFullSourceTower.direction F (f u) t.val := by
    funext t r i
    exact FlatAffineFullSourceContext.direction_comp F f u t.val r i
  have hb : (fun t : Fin (F.depth (f u)) => FlatAffineFullSourceTower.level (FlatAffineFullSourceContext.comp F f) u t.val) =
      fun t : Fin (F.depth (f u)) => FlatAffineFullSourceTower.level F (f u) t.val := by
    funext t j
    exact FlatAffineFullSourceContext.level_comp F f u t.val j
  unfold rawSystem
  erw [FlatAffineFullSourceContext.polynomial_comp, hs, ha, hb]
  rfl

lemma system_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool)
    (i : Fin (FlatAffineFullSourcePositive.count F (f u))) :
    system (FlatAffineFullSourceContext.comp F f) u i = system F (f u) i := by
  unfold system
  rw [rawSystem_comp]

lemma degree_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool)
    (i : Fin (FlatAffineFullSourcePositive.count F (f u))) :
    degree (FlatAffineFullSourceContext.comp F f) u i = degree F (f u) i := rfl

noncomputable def frame (F : Inputs) : Inputs := FlatAffineFullSourceContext.comp F pairFst

theorem integer_evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W)
    (row : (c : List Bool) → Fin (FlatAffineFullSourcePositive.count F c)) (hr : UnaryFn (fun c => (row c).val))
    {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    SpaceFunction (HomogenizationPolynomialBits.integerValue (FlatAffineFullSourcePositive.count F) W
      (fun c => system F c (row c)) modulus) := by
  let row' : (q : List Bool) → Fin (FlatAffineFullSourcePositive.count (frame F) q) := fun q => row (pairFst q)
  have E := evaluator (FlatAffineFullSourceContext.access h pairFst_mem_FP) row'
    (hr.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP) pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hm)
  refine E.congr (funext fun q => ?_)
  simp only [FixedWidthRowBits.value, HomogenizationPolynomialBits.integerValue]
  have hs := system_comp F pairFst q (row (pairFst q))
  dsimp +instances only [frame, row', FlatAffineFullSourcePositive.count, FlatAffineFullSourceTower.count,
    FlatAffineFullSourceTower.stageWidth, FlatAffineFullSourceTower.arity, FlatAffineFullSourceContext.comp,
    BoundedFullWriter.Readers.comp] at hs ⊢
  rw [hs]
  rfl

noncomputable def homogeneousRow (F : Inputs)
    (row : (c : List Bool) → Fin (FlatAffineFullSourcePositive.count F c)) (u : List Bool) :
    MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u + 1)) (Polynomial ℤ) :=
  HomogenizationPolynomialBits.polynomial (FlatAffineFullSourcePositive.count F) (fun c => degree F c (row c))
    (fun c => system F c (row c)) u

theorem homogeneous_evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W)
    (row : (c : List Bool) → Fin (FlatAffineFullSourcePositive.count F c)) (hr : UnaryFn (fun c => (row c).val))
    {parameter modulus : List Bool → List Bool} (hk : parameter ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (HomogenizationPolynomialBits.value (FlatAffineFullSourcePositive.count F) W
      (fun c => degree F c (row c)) (fun c => system F c (row c)) parameter modulus) :=
  HomogenizationPolynomialBits.evaluator (FlatAffineFullSourcePositive.count_unary h) hW
    (BinaryFn.ofUnary (degree_unary h row hr)) _ parameter modulus hk (integer_evaluator h hW row hr hm)

end LeanCanny.Encoding.FlatAffinePowerPositive
