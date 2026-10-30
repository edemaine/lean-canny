/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteDegree
public import LeanCanny.Algebra.BivariateAtZeroSpace

/-! # Native coordinate eliminants of the joint finite midpoint system

Canonical Gram controls use the stored exact retained degrees. A zero
parameter specialization gives integer coordinate polynomials with native
coefficients. Valid frames capture all real roots and keep each coordinate
polynomial nonzero, including at singular roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteGram
open LeanCanny.Algebra LeanCanny.Computation MatrixPower Polynomial
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def coordinate (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (s : List Bool)
    (i : Fin (FlatAffineEndpointFiniteFrame.arity F s)) : (ℤ[X])[X] :=
  Geometry.AffineShiftCoordinates.coordinate (FlatAffineEndpointFiniteFrame.system F height s) (fun _ => 0)
    (FlatAffineEndpointFiniteFrame.degrees F s) i

noncomputable def family (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (index : (s : List Bool) → Fin (FlatAffineEndpointFiniteFrame.arity F s)) : AffineShiftCoordinateBits.Family where
  arity := FlatAffineEndpointFiniteFrame.arity F
  width s := AffineRingCoordinates.width (FlatAffineEndpointFiniteFrame.degrees F s)
  degree := FlatAffineEndpointFiniteDegree.degree F
  rows := FlatAffineEndpointFiniteFrame.system F height
  shifts _ _ := 0
  coordinate := index

theorem degrees_eq (F : Inputs) (s : List Bool) :
    (fun i : Fin (FlatAffineEndpointFiniteFrame.arity F s) => FlatAffineEndpointFiniteDegree.degree F s i.val) =
      FlatAffineEndpointFiniteFrame.degrees F s := by
  funext i
  exact congrArg (FlatAffineEndpointFiniteFrame.degrees F s) (FlatAffineEndpointFiniteDegree.rowAt_val F s i)

theorem width_eq (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (index : (s : List Bool) → Fin (FlatAffineEndpointFiniteFrame.arity F s)) (s : List Bool) :
    (family F height index).width s = AffineRingCoordinates.width
      (fun i : Fin ((family F height index).arity s) => (family F height index).degree s i.val) := by
  exact congrArg AffineRingCoordinates.width (degrees_eq F s).symm

theorem controls {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (index : (s : List Bool) → Fin (FlatAffineEndpointFiniteFrame.arity F s)) :
    (family F height index).parameter.affine.homogeneous.layout.Controls :=
  (family F height index).controls (FlatAffineEndpointFiniteFrame.arity_unary h)
    (FlatAffineEndpointFiniteDegree.degree_binary h) (width_eq F height index)

theorem originalEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (index : (s : List Bool) → Fin (FlatAffineEndpointFiniteFrame.arity F s)) :
    SpaceFunction (family F height index).integerCoefficient := by
  let G := family F height index
  have A := controls h height index
  exact FlatAffineEndpointFiniteRows.rowEvaluator h height hh AffineValueGramBits.base AffineValueGramBits.base_FP
    G.row (G.row_unary A) (A.width.comp AffineValueGramBits.base_FP)
    MacaulayFullBoxBits.shift_FP (mem_FP_comp MacaulayFullBoxBits.ctx_FP pairSnd_mem_FP)

theorem shiftEvaluator (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (index : (s : List Bool) → Fin (FlatAffineEndpointFiniteFrame.arity F s)) :
    SpaceFunction (family F height index).shiftCoefficient := by
  refine (SpaceFunction.ofFP _ (constFn_mem_FP [])).congr (funext fun q => ?_)
  simp [AffineShiftCoordinateBits.Family.shiftCoefficient, AffineShiftCoordinateBits.Family.selectedShift,
    PolynomialParameterShiftBits.scalar, family, residueBits, BinaryNatCode.encode]

noncomputable def reader {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (index : (s : List Bool) → Fin (FlatAffineEndpointFiniteFrame.arity F s))
    (hi : UnaryFn (fun s => (index s).val)) : CertifiedPolynomial.BivariateReader (fun s => coordinate F height s (index s)) := by
  let G := family F height index
  have E := G.canonicalReader (FlatAffineEndpointFiniteFrame.arity_unary h) (FlatAffineEndpointFiniteDegree.degree_binary h)
    hi (fun _ => 0) (BinaryFn.const 0) (fun _ _ => by change (0 : Polynomial ℤ).natDegree ≤ 0; simp) (width_eq F height index)
    (originalEvaluator h height hh index) (shiftEvaluator F height index)
  have he : (fun s => Geometry.AffineShiftCoordinates.coordinate (G.rows s) (G.shifts s)
      (fun i => G.degree s i.val) (G.coordinate s)) = (fun s => coordinate F height s (index s)) := by
    funext s
    exact congrArg (fun d : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℕ =>
      Geometry.AffineShiftCoordinates.coordinate (FlatAffineEndpointFiniteFrame.system F height s) (fun _ => 0) d (index s))
      (degrees_eq F s)
  exact he ▸ E

noncomputable def annihilator (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (s : List Bool)
    (i : Fin (FlatAffineEndpointFiniteFrame.arity F s)) : ℤ[X] := (coordinate F height s i).map Polynomial.constantCoeff

theorem evaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (index : (s : List Bool) → Fin (FlatAffineEndpointFiniteFrame.arity F s))
    (hi : UnaryFn (fun s => (index s).val)) :
    SpaceFunction (PrimitivePairBits.coefficient (fun s => annihilator F height s (index s))) :=
  BivariateAtZeroBits.evaluator (reader h height hh index hi)

theorem ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (i : Fin (FlatAffineEndpointFiniteFrame.arity F s)) : annihilator F height s i ≠ 0 := by
  have hl : SymbolicScaledSquarefree.scalarEvaluation 0 (coordinate F height s i).leadingCoeff ≠ 0 :=
    ne_of_gt (Geometry.AffineShiftCoordinates.positive_leading (FlatAffineEndpointFiniteFrame.system F height s)
    (fun _ => 0) (FlatAffineEndpointFiniteFrame.degrees F s) (FlatAffineEndpointFiniteFrame.degrees_pos F height s hs)
    (FlatAffineEndpointFiniteFrame.noInfinity F hcone height s hs) i 0)
  have hn : (coordinate F height s i).map (SymbolicScaledSquarefree.scalarEvaluation 0) ≠ 0 := by
    intro hz
    have H := congrArg Polynomial.leadingCoeff hz
    rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hl, Polynomial.leadingCoeff_zero] at H
    exact hl H
  intro hz
  have H := congrArg (fun p : ℤ[X] => p.map (Int.castRingHom ℝ)) hz
  simp only [annihilator, Polynomial.map_zero] at H
  rw [BivariateAtZeroBits.map_real] at H
  exact hn H

theorem root (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (s : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s) (z : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ)
    (hz : ∀ i, (FlatAffineEndpointFiniteFrame.system F height s i).eval₂ (Int.castRingHom ℝ) z = 0)
    (i : Fin (FlatAffineEndpointFiniteFrame.arity F s)) : (annihilator F height s i).eval₂ (Int.castRingHom ℝ) (z i) = 0 := by
  rw [annihilator, BivariateAtZeroBits.real_eval]
  have hx := (Geometry.AffineShiftCoordinates.roots_iff (FlatAffineEndpointFiniteFrame.system F height s) (fun _ => 0) 0 z).mpr
    (fun j => by simpa only [map_zero] using hz j)
  have H := congrFun (Geometry.AffineShiftCoordinates.capture (FlatAffineEndpointFiniteFrame.system F height s) (fun _ => 0)
    (FlatAffineEndpointFiniteFrame.degrees F s) (FlatAffineEndpointFiniteFrame.degree_bound F height s hs) 0 z hx) i
  simpa only [coordinate, Geometry.SquarefreeRootFamily.value_apply, Pi.zero_apply] using H

end LeanCanny.Encoding.FlatAffineEndpointFiniteGram
