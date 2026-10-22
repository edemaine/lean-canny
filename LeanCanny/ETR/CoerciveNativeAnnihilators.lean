/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveAnnihilatorControls

/-! # Pinning the perturbation coordinate in the symbolic root product

The first coordinate has polynomial T-alpha. Spatial coordinates use the
canonical coercive annihilants. This preserves the integer sample-query
layout: its first variable is still the perturbation coordinate.
-/

@[expose] public section
namespace LeanCanny.ETR.CoerciveNativeAnnihilators
open Polynomial LeanCanny.Algebra
open CoerciveSourceSampling CoerciveAnnihilatorControls
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det Macaulay.fullMatrix

noncomputable def pin : Polynomial (Polynomial ℤ) := X - C X
noncomputable def original (bits : List Bool) : ℕ → Polynomial (Polynomial ℤ)
  | 0 => pin
  | i + 1 => CoerciveAnnihilatorControls.original bits i

theorem pin_ne_zero : pin ≠ 0 := by
  intro hz
  have h := congrArg (fun p : Polynomial (Polynomial ℤ) => p.coeff 1) hz
  simp [pin] at h

theorem pin_root_iff (s t : ℝ) :
    pin.eval₂ (SymbolicScaledSquarefree.scalarEvaluation s) t = 0 ↔ t = s := by
  simp [pin, SymbolicScaledSquarefree.scalarEvaluation, sub_eq_zero]

theorem original_ne_zero (bits : List Bool) (i : ℕ) : original bits i ≠ 0 := by
  cases i with
  | zero => exact pin_ne_zero
  | succ i => exact CoerciveAnnihilatorControls.original_ne_zero bits i

noncomputable def massExponent (bits : List Bool) : ℕ := CoerciveAnnihilatorControls.massExponent bits + 1

theorem massExponent_binary : BinaryFn massExponent :=
  CoerciveAnnihilatorControls.massExponent_binary.add (BinaryFn.const 1)

theorem original_mass (bits : List Bool) (i : ℕ) :
    NestedMass.mass (original bits i) ≤ 2 ^ massExponent bits := by
  cases i with
  | zero =>
    have h : NestedMass.mass pin ≤ 2 := by
      apply (NestedMass.sub_le _ _).trans
      change NestedMass.mass (Polynomial.monomial 1 (1 : Polynomial ℤ)) +
        NestedMass.mass (Polynomial.C (Polynomial.monomial 1 (1 : ℤ))) ≤ 2
      simp only [NestedMass.monomial, NestedMass.C, coefficientMass_monomial]
      have hone : coefficientMass (1 : Polynomial ℤ) = 1 := by
        change coefficientMass (Polynomial.C (1 : ℤ)) = 1
        rw [coefficientMass_C]
        rfl
      rw [hone]
      decide
    have h2 : 2 ≤ 2 ^ massExponent bits := by
      have ht := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
        (show 1 ≤ massExponent bits by unfold massExponent; omega)
      simpa only [pow_one] using ht
    exact h.trans h2
  | succ i =>
    exact (CoerciveAnnihilatorControls.original_mass bits i).trans
      (Nat.pow_le_pow_right (by decide) (by unfold massExponent; omega))

theorem original_coefficient_mass (bits : List Bool) (i k : ℕ) :
    coefficientMass ((original bits i).coeff k) ≤ 2 ^ massExponent bits :=
  (NestedMass.coeff_le _ _).trans (original_mass bits i)

private theorem pin_degree : pin.natDegree ≤ 1 := by
  exact (Polynomial.natDegree_sub_le _ _).trans (by simp)

private theorem pin_inner_degree (k : ℕ) : (pin.coeff k).natDegree ≤ 1 := by
  by_cases hk0 : k = 0
  · simp [pin, hk0]
  · by_cases hk1 : k = 1
    · simp [pin, hk1]
    · simp [pin, Polynomial.coeff_X, Polynomial.coeff_C, hk0, Ne.symm hk1]

noncomputable def degreeBound (bits : List Bool) : ℕ := CoerciveAnnihilatorControls.degreeBound bits + 1

theorem degreeBound_binary : BinaryFn degreeBound :=
  CoerciveAnnihilatorControls.degreeBound_binary.add (BinaryFn.const 1)

theorem original_degree (bits : List Bool) (i : ℕ) : (original bits i).natDegree ≤ degreeBound bits := by
  cases i with
  | zero => exact pin_degree.trans (by unfold degreeBound; omega)
  | succ i => exact (CoerciveAnnihilatorControls.original_degree bits i).trans (by unfold degreeBound; omega)

theorem original_inner_degree (bits : List Bool) (i k : ℕ) :
    ((original bits i).coeff k).natDegree ≤ degreeBound bits := by
  cases i with
  | zero => exact (pin_inner_degree k).trans (by unfold degreeBound; omega)
  | succ i => exact (CoerciveAnnihilatorControls.original_inner_degree bits i k).trans (by unfold degreeBound; omega)

theorem critical_roots (bits : List Bool) (s : ℝ) (x : Fin (dimension bits) → ℝ)
    (hx : ∀ j, MvPolynomial.eval x (MvPolynomial.pderiv j
      (CoerciveCriticalFibers.polynomial ((polynomial bits).map (Int.castRingHom ℝ))
        (degreeAllowance bits) s)) = 0)
    (i : Fin (dimension bits + 1)) :
    (original bits i.val).eval₂ (SymbolicScaledSquarefree.scalarEvaluation s) ((Fin.cons s x : Fin (dimension bits + 1) → ℝ) i) = 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [original, pin, SymbolicScaledSquarefree.scalarEvaluation]
  · change (CoerciveAnnihilatorControls.original bits j.val).eval₂ _ (x j) = 0
    rw [CoerciveAnnihilatorControls.original, dite_eq_left j.isLt]
    exact CoerciveBoxGramEliminant.symbolic_eval_eq_zero _ _ (polynomial_degree bits) j s x hx

end LeanCanny.ETR.CoerciveNativeAnnihilators
