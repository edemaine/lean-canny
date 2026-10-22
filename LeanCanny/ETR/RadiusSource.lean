/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.PerturbedSource
public import LeanCanny.Geometry.CriticalEnergyPolynomial

/-! # Joint-radius submersions and singular-radius critical values for ETR

The free-radius joint family has surjective derivatives at nonzero radius.
For each active set, singular fixed-radius points give critical values of an
explicit integer sum-of-squares polynomial. A certified FP degree bound is
derived from the normalized compiler output. Finiteness of the critical values
and an effective good-radius interval are still required.
-/

@[expose] public section

namespace LeanCanny.ETR.RadiusSource

open LeanCanny.Encoding
open Geometry

theorem joint_derivative_surjective (bits : List Bool) (epsilon : ℝ) (z : PerturbedSource.Point bits × ℝ)
    (hd : z.2 ≠ 0) :
    Function.Surjective (fderiv ℝ (PolynomialPerturbation.jointConstraintMap (CompactSource.polynomial bits) epsilon) z) :=
  PolynomialPerturbation.jointConstraintMap_derivative_surjective _ _ _ hd

theorem active_derivative_criterion (bits : List Bool) (epsilon delta : ℝ)
    (s : Finset (PerturbedSource.Index bits)) (z : PerturbedSource.Point bits) :
    Function.Surjective (fderiv ℝ (ActiveRadius.fixedMap
      (PolynomialPerturbation.constraintMap (CompactSource.polynomial bits) epsilon) s delta) z) ↔
      (∃ j, j ∉ s ∧ z.2 j ≠ 0) ∨ (SquaredRadius.derivative z.2).comp
        (fderiv ℝ (PolynomialPerturbation.constraintMap (CompactSource.polynomial bits) epsilon) z.1) ≠ 0 :=
  ActiveRadius.fderiv_surjective_iff _ _ _ _
    (((PolynomialPerturbation.contDiff_constraintMap _ _).differentiable (by simp)) z.1)

theorem singular_implies_critical (bits : List Bool) (epsilon delta : ℝ)
    (s : Finset (PerturbedSource.Index bits)) (z : PerturbedSource.Point bits)
    (hz : z ∈ PerturbedSource.feasible bits epsilon delta)
    (ha : ∀ i ∈ s, PolynomialPerturbation.parameterMap (CompactSource.polynomial bits) epsilon z i = 0)
    (hs : ¬ Function.Surjective (fderiv ℝ (ActiveRadius.fixedMap
      (PolynomialPerturbation.constraintMap (CompactSource.polynomial bits) epsilon) s delta) z)) :
    ActiveRadius.energy (PolynomialPerturbation.constraintMap (CompactSource.polynomial bits) epsilon) s z.1 = delta ^ 2 ∧
      fderiv ℝ (ActiveRadius.energy (PolynomialPerturbation.constraintMap (CompactSource.polynomial bits) epsilon) s) z.1 = 0 :=
  ActiveRadius.singular_implies_critical _ _ _ _
    (((PolynomialPerturbation.contDiff_constraintMap _ _).differentiable (by simp)) z.1) ha hz.2 hs

noncomputable def energyPolynomial (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) :
    MvPolynomial (PerturbedSource.Variable bits) ℤ :=
  PolynomialPerturbation.energyPolynomial (CompactSource.polynomial bits) s

theorem eval_energyPolynomial (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (epsilon delta : ℝ) (z : PerturbedSource.Point bits) :
    (energyPolynomial bits s).eval₂ (Int.castRingHom ℝ) (PolynomialPerturbation.assignment epsilon delta z) =
      ActiveRadius.energy (PolynomialPerturbation.constraintMap (CompactSource.polynomial bits) epsilon) s z.1 :=
  PolynomialPerturbation.eval_energyPolynomial _ _ _ _ _

def degreeCode (bits : List Bool) : List Bool := BinaryNatCode.encode (8 * CompactSource.size bits ^ 2 + 4)

theorem degreeCode_FP : degreeCode ∈ FP := by
  have h := bits_mem_FP (((UnaryFn.const 8).mul (CompactSource.size_unary.pow_const 2)).add (UnaryFn.const 4))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem energy_degree_le_code (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) :
    (energyPolynomial bits s).totalDegree ≤ Nat.fromBitsLE (degreeCode bits) := by
  have h := PolynomialPerturbation.energyPolynomial_degree (CompactSource.polynomial bits) s
  have hp := CompactSource.polynomial_degree bits
  simp only [degreeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, CompactSource.size_eq]
  exact h.trans (by omega)

end LeanCanny.ETR.RadiusSource
