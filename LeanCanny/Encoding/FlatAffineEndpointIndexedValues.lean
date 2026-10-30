/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointTrailing
public import LeanCanny.Geometry.FlatAffineEndpointMidpoint

/-! # Uniform native midpoint-factor indexing

An extra index field selects any original coordinate while retaining the
prepared source record. The reader charges both Gram stages and the native
trailing-coefficient scan, uniformly in that coordinate index.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointIndexedValues
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open MacaulayFullBoxBits (ctx shift uv ctx_FP shift_FP uv_FP)
open AffineValueGramBits (base base_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def index (F : Inputs) (z : List Bool) : Fin (count F (pairFst (pairFst z))) :=
  FlatAffineHeightGram.rawRow F (pairFst (pairFst z)) (Nat.fromBitsLE (pairSnd z))

theorem index_unary {F : Inputs} (h : F.Access) : UnaryFn (fun z => (index F z).val) :=
  UnaryFn.fromBitsLE_min pairSnd_mem_FP (((FlatAffineFullSourcePositive.count_unary h).comp
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).sub (UnaryFn.const 1))

noncomputable def family (F : Inputs) (height : (u : List Bool) → Fin (count F u)) : IntegerGridValueGramBits.Family where
  arity z := FlatAffineEndpointRows.arity F (pairFst z)
  width z := FlatAffineEndpointValues.width F (pairFst z)
  degree z _ := FlatAffineEndpointValues.coordinateDegree F (pairFst z)
  testDegree _ := 1
  coordinate z := FlatAffineEndpointGrid.coordinate F height (pairFst z)
  test z := (FrozenAffineCopies.midpoint (index F z)).map Polynomial.C

theorem controls {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) :
    (family F height).affine.homogeneous.layout.Controls :=
  (family F height).affine.homogeneous.uniform_controls (FlatAffineEndpointValues.coordinateDegree F ∘ pairFst)
    ((FlatAffineEndpointRows.arity_unary h).comp pairFst_mem_FP)
    ((FlatAffineEndpointValues.coordinateDegree_binary h height).comp pairFst_mem_FP) (BinaryFn.const 1)
    (fun _ _ => rfl) (fun _ => rfl)

theorem testEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) :
    SpaceFunction (family F height).testCoefficient := by
  let G := family F height
  have hG := controls h height
  have hp := mem_FP_comp base_FP (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have hn := (FlatAffineFullSourcePositive.count_unary h).comp hp
  have EP := FrozenAffineMidpointBits.evaluator hn (hG.width.comp base_FP)
    (fun q => index F (base q)) ((index_unary h).comp base_FP) shift_FP (mem_FP_comp ctx_FP pairSnd_mem_FP)
  have hz := (BinaryFn.fromBits (mem_FP_comp uv_FP pairFst_mem_FP)).eq (BinaryFn.const 0)
  have H := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (pairFst (uv q)) = 0)) hz.flag_mem_FP
    EP (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine H.congr (funext fun q => ?_)
  let a : ℤ := (FrozenAffineCopies.midpoint (index F (base q))).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (FlatAffineEndpointRows.arity F (pairFst (base q)))))
      (FlatAffineEndpointValues.width F (pairFst (base q))) (Nat.fromBitsLE (shift q)))
  change (if decide (Nat.fromBitsLE (pairFst (uv q)) = 0) then residueBits (a : ZMod (Nat.fromBitsLE (pairSnd (ctx q)) + 1)) else []) =
    residueBits (((Polynomial.C a).coeff (Nat.fromBitsLE (pairFst (uv q)))) : ZMod (Nat.fromBitsLE (pairSnd (ctx q)) + 1))
  by_cases hk : Nat.fromBitsLE (pairFst (uv q)) = 0
  · simp only [decide_eq_true_eq, Polynomial.coeff_C, hk, ite_true]
  · simp only [decide_eq_true_eq, Polynomial.coeff_C, hk, ite_false, Int.cast_zero, residueBits, ZMod.val_zero]
    rfl

noncomputable def polynomial (F : Inputs) (height : (u : List Bool) → Fin (count F u)) :=
  (family F height).affine.homogeneous.annihilator

theorem polynomial_eq (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    polynomial F height z = FlatAffineEndpointTrailing.polynomial F height
      (fun r => FlatAffineHeightGram.rawRow F (pairFst r) (Nat.fromBitsLE (pairSnd z))) (pairFst z) := rfl

noncomputable def reader {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : CertifiedPolynomial.BivariateReader (polynomial F height) := by
  have EC := DiagonalParameterBits.coefficient_comp_evaluator (FlatAffineEndpointRows.arity F)
    (FlatAffineEndpointGrid.coordinate F height) pairFst pairFst_mem_FP (FlatAffineEndpointGrid.coefficientEvaluator h height hh)
  apply (family F height).reader (controls h height) (FlatAffineEndpointValues.coordinateDegree F ∘ pairFst)
    ((FlatAffineEndpointValues.coordinateDegree_binary h height).comp pairFst_mem_FP) ?_ ?_ EC (testEvaluator h height)
  · intro z i k
    exact FlatAffineEndpointValues.coordinate_inner_bound F height (pairFst z) i k
  · intro z e
    change (Polynomial.C ((FrozenAffineCopies.midpoint (index F z)).coeff e)).natDegree ≤ _
    simp only [Polynomial.natDegree_C]
    exact Nat.zero_le _

theorem degree_le (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    (polynomial F height z).natDegree ≤ FlatAffineEndpointTrailing.outerBound F (pairFst z) := by
  rw [polynomial_eq]
  exact FlatAffineEndpointValues.degree_le F height _ _

theorem parameter_degree_le (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) (k : ℕ) :
    ((polynomial F height z).coeff k).natDegree ≤ FlatAffineEndpointTrailing.innerBound F (pairFst z) := by
  rw [polynomial_eq]
  exact FlatAffineEndpointValues.parameter_degree_le F height _ _ k

theorem height_le (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) (j k : ℕ) :
    ((((polynomial F height z).coeff j).coeff k).natAbs).size ≤ FlatAffineEndpointValueBounds.heightBound F (pairFst z) := by
  rw [polynomial_eq]
  exact FlatAffineEndpointValueBounds.height_le F height _ _ j k

theorem valueEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (PolynomialTrailingCoefficientBits.value (polynomial F height)) :=
  PolynomialTrailingCoefficientBits.evaluator _ (reader h height hh)
    ((FlatAffineEndpointTrailing.outerBound_binary h height (fun r => height (pairFst r))).comp pairFst_mem_FP)
    ((FlatAffineEndpointTrailing.innerBound_binary h height (fun r => height (pairFst r))).comp pairFst_mem_FP)
    ((FlatAffineEndpointValueBounds.heightBound_binary h height (fun r => height (pairFst r))).comp pairFst_mem_FP)
    (degree_le F height) (parameter_degree_le F height) (height_le F height)

noncomputable def trailing (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) : Polynomial ℤ :=
  (polynomial F height z).trailingCoeff

theorem coefficientEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (PrimitivePairBits.coefficient (trailing F height)) := by
  let prepare := FlatAffineEndpointTrailing.primitiveQuery
  refine ((valueEvaluator h height hh).precompose prepare FlatAffineEndpointTrailing.primitiveQuery_FP).congr (funext fun q => ?_)
  let read (r k m : List Bool) := residueBits (((polynomial F height r).trailingCoeff.coeff (Nat.fromBitsLE k)) : ZMod (Nat.fromBitsLE m + 1))
  change read (pairFst (pairFst (prepare q))) (pairSnd (prepare q)) (pairSnd (pairFst (prepare q))) =
    read (pairFst (pairFst q)) (pairSnd (pairFst q)) (pairSnd q)
  simp only [prepare, FlatAffineEndpointTrailing.primitiveQuery, pairFst_pair, pairSnd_pair]

theorem trailing_ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (z : List Bool)
    (hr : FlatAffineEndpointValidity.Valid F height (pairFst z)) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst z))) = 0) :
    trailing F height z ≠ 0 := by
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
  rw [polynomial_eq]
  exact Geometry.FlatAffineEndpointMidpoint.nonzero F hcone height _ (pairFst z) hr a ha

end LeanCanny.Encoding.FlatAffineEndpointIndexedValues
