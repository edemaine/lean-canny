/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SeparatedPowerPotential
public import LeanCanny.Algebra.PartialDerivativeDegree
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Tactic.Ring

/-! # The actual pure-power critical equations of the deformation -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial
open scoped Classical BigOperators

variable {S : Type*} [CommRing S] {n : ℕ}

@[expose] noncomputable def potentialPolynomial (ell : ℕ) (a : Fin n → S) :
    MvPolynomial (Fin n) S :=
  ∑ i, (X i ^ (ell + 1) - C ((ell + 1 : ℕ) * a i ^ ell) * X i +
    C ((ell + 1 : ℕ) * a i ^ (ell + 1)))

@[expose] noncomputable def deformedPolynomial (ell : ℕ) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) : MvPolynomial (Fin n) S :=
  potentialPolynomial ell a + C ((ell + 1 : ℕ) * u) * F

@[expose] noncomputable def criticalLower (ell : ℕ) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (i : Fin n) : MvPolynomial (Fin n) S :=
  C (a i ^ ell) - C u * pderiv i F

theorem pderiv_potentialPolynomial (ell : ℕ) (a : Fin n → S) (j : Fin n) :
    pderiv j (potentialPolynomial ell a) =
      C ((ell + 1 : ℕ) : S) * (X j ^ ell - C (a j ^ ell)) := by
  have hentry (i : Fin n) : pderiv j
      (X i ^ (ell + 1) - C ((ell + 1 : ℕ) * a i ^ ell) * X i +
        C ((ell + 1 : ℕ) * a i ^ (ell + 1))) =
      if i = j then C ((ell + 1 : ℕ) : S) * (X j ^ ell - C (a j ^ ell)) else 0 := by
    by_cases hij : i = j
    · subst i
      simp only [map_add, map_sub, pderiv_pow, pderiv_C_mul, pderiv_X_self,
        pderiv_C, Nat.add_sub_cancel, mul_one, add_zero, ↓reduceIte]
      simp only [map_mul, map_natCast]
      ring
    · simp [hij]
  rw [potentialPolynomial, map_sum]
  simp_rw [hentry]
  simp

theorem pderiv_deformedPolynomial (ell : ℕ) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (i : Fin n) :
    pderiv i (deformedPolynomial ell a u F) =
      C ((ell + 1 : ℕ) : S) * (X i ^ ell - criticalLower ell a u F i) := by
  rw [deformedPolynomial, map_add, pderiv_potentialPolynomial, pderiv_C_mul,
    criticalLower, map_mul]
  ring

theorem criticalLower_degree (ell : ℕ) (hell : 1 ≤ ell) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (hF : F.totalDegree ≤ ell) (i : Fin n) :
    (criticalLower ell a u F i).totalDegree < ell := by
  have hp := LeanCanny.Algebra.PartialDerivativeDegree.degree_le F i
  have hm := totalDegree_mul (C u) (pderiv i F)
  rw [totalDegree_C] at hm
  have hs := totalDegree_sub (C (a i ^ ell)) (C u * pderiv i F)
  rw [totalDegree_C] at hs
  change (C (a i ^ ell) - C u * pderiv i F).totalDegree < ell
  omega

theorem eval_potentialPolynomial (ell : ℕ) (a x : Fin n → ℝ) :
    eval x (potentialPolynomial ell a) = separatedPotential ell a x := by
  simp only [potentialPolynomial, map_sum, map_add, map_sub, map_mul, map_pow,
    eval_X, eval_C, separatedPotential, powerPotential]

theorem eval_deformedPolynomial (ell : ℕ) (a x : Fin n → ℝ) (u : ℝ)
    (F : MvPolynomial (Fin n) ℝ) :
    eval x (deformedPolynomial ell a u F) =
      separatedPotential ell a x + (ell + 1 : ℕ) * u * eval x F := by
  simp only [deformedPolynomial, map_add, map_mul, eval_C, eval_potentialPolynomial,
    mul_assoc]

end LeanCanny.CountingHierarchy
