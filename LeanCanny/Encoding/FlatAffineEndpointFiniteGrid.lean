/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteGram

/-! # Indexed native coordinates of the joint finite midpoint frame

The coordinate index is extra query metadata. Both retained equations and
all original rows keep the same prepared source record throughout the Gram
computation and the final integer specialization.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteGrid
open LeanCanny.Algebra LeanCanny.Computation MatrixPower Polynomial
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def family (F : Inputs) (height : (u : List Bool) → Fin (count F u)) : AffineShiftCoordinateBits.Family where
  arity z := FlatAffineEndpointFiniteFrame.arity F (pairFst z)
  width z := AffineRingCoordinates.width (FlatAffineEndpointFiniteFrame.degrees F (pairFst z))
  degree z := FlatAffineEndpointFiniteDegree.degree F (pairFst z)
  rows z := FlatAffineEndpointFiniteFrame.system F height (pairFst z)
  shifts _ _ := 0
  coordinate := FlatAffineEndpointFiniteDegree.indexRow F

def degreeQuery (q : List Bool) : List Bool := pair (pairFst (pairFst q)) (pairSnd q)
theorem degreeQuery_FP : degreeQuery ∈ FP := by polytime [degreeQuery]

theorem degree_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) :
    BinaryFn (fun q => (family F height).degree (pairFst q) (Nat.fromBitsLE (pairSnd q))) := by
  apply BinaryFn.of_eq ((FlatAffineEndpointFiniteDegree.degree_binary h).comp degreeQuery_FP)
  intro q
  simp only [Function.comp_apply, degreeQuery, pairFst_pair, pairSnd_pair]
  rfl

theorem width_eq (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    (family F height).width z = AffineRingCoordinates.width
      (fun i : Fin ((family F height).arity z) => (family F height).degree z i.val) :=
  congrArg AffineRingCoordinates.width (FlatAffineEndpointFiniteGram.degrees_eq F (pairFst z)).symm

theorem controls {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) :
    (family F height).parameter.affine.homogeneous.layout.Controls :=
  (family F height).controls ((FlatAffineEndpointFiniteFrame.arity_unary h).comp pairFst_mem_FP)
    (degree_binary h height) (width_eq F height)

theorem originalEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (family F height).integerCoefficient := by
  let G := family F height
  have A := controls h height
  exact FlatAffineEndpointFiniteRows.rowEvaluator h height hh (pairFst ∘ AffineValueGramBits.base)
    (mem_FP_comp AffineValueGramBits.base_FP pairFst_mem_FP) G.row (G.row_unary A)
    (A.width.comp AffineValueGramBits.base_FP) MacaulayFullBoxBits.shift_FP (mem_FP_comp MacaulayFullBoxBits.ctx_FP pairSnd_mem_FP)

theorem shiftEvaluator (F : Inputs) (height : (u : List Bool) → Fin (count F u)) :
    SpaceFunction (family F height).shiftCoefficient := by
  refine (SpaceFunction.ofFP _ (constFn_mem_FP [])).congr (funext fun q => ?_)
  simp [AffineShiftCoordinateBits.Family.shiftCoefficient, AffineShiftCoordinateBits.Family.selectedShift,
    PolynomialParameterShiftBits.scalar, family, residueBits, BinaryNatCode.encode]

noncomputable def indexed (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) : (ℤ[X])[X] :=
  FlatAffineEndpointFiniteGram.coordinate F height (pairFst z) (FlatAffineEndpointFiniteDegree.indexRow F z)

noncomputable def reader {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : CertifiedPolynomial.BivariateReader (indexed F height) := by
  let G := family F height
  have E := G.canonicalReader ((FlatAffineEndpointFiniteFrame.arity_unary h).comp pairFst_mem_FP) (degree_binary h height)
    (FlatAffineEndpointFiniteDegree.indexRow_unary h) (fun _ => 0) (BinaryFn.const 0)
    (fun _ _ => by change (0 : Polynomial ℤ).natDegree ≤ 0; simp) (width_eq F height)
    (originalEvaluator h height hh) (shiftEvaluator F height)
  have he : (fun z => Geometry.AffineShiftCoordinates.coordinate (G.rows z) (G.shifts z)
      (fun i => G.degree z i.val) (G.coordinate z)) = indexed F height := by
    funext z
    exact congrArg (fun d : Fin (FlatAffineEndpointFiniteFrame.arity F (pairFst z)) → ℕ =>
      Geometry.AffineShiftCoordinates.coordinate (FlatAffineEndpointFiniteFrame.system F height (pairFst z)) (fun _ => 0)
        d (FlatAffineEndpointFiniteDegree.indexRow F z)) (FlatAffineEndpointFiniteGram.degrees_eq F (pairFst z))
  exact he ▸ E

noncomputable def rawAnnihilator (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (i : ℕ) : ℤ[X] :=
  FlatAffineEndpointFiniteGram.annihilator F height s (FlatAffineEndpointFiniteDegree.rowAt F s i)

noncomputable def annihilator (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) : ℤ[X] :=
  rawAnnihilator F height (pairFst z) (Nat.fromBitsLE (pairSnd z))

theorem packet (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (s i : List Bool) :
    annihilator F height (pair s i) = rawAnnihilator F height s (Nat.fromBitsLE i) := by
  simp only [annihilator, pairFst_pair, pairSnd_pair]

theorem evaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (PrimitivePairBits.coefficient (annihilator F height)) :=
  BivariateAtZeroBits.evaluator (reader h height hh)

end LeanCanny.Encoding.FlatAffineEndpointFiniteGrid
