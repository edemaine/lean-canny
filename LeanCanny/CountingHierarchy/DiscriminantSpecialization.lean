/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.FieldTheory.Separable

/-! # Specialization of a monic polynomial's derivative resultant -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial

variable {R K : Type*} [CommRing R] [IsDomain R] [CharZero R] [Field K] [CharZero K]

theorem resultant_derivative_map_of_monic (φ : R →+* K) (p : R[X]) (hp : p.Monic) :
    (p.map φ).resultant (p.map φ).derivative = φ (p.resultant p.derivative) := by
  simp only [Polynomial.natDegree_derivative, hp.natDegree_map φ]
  rw [Polynomial.derivative_map]
  exact Polynomial.resultant_map_map p p.derivative p.natDegree (p.natDegree - 1) φ

/-- One separable specialization proves that the parameter discriminant
 polynomial is nonzero, without requiring the coefficient map to be injective. -/
theorem resultant_derivative_ne_zero_of_separable_map (φ : R →+* K) (p : R[X])
    (hp : p.Monic) (hsep : (p.map φ).Separable) : p.resultant p.derivative ≠ 0 := by
  intro hz
  apply Polynomial.resultant_ne_zero (p.map φ) (p.map φ).derivative hsep
  rw [resultant_derivative_map_of_monic φ p hp, hz, map_zero]

/-- Avoiding a zero of the parameter discriminant guarantees a separable
 specialized polynomial. -/
theorem separable_map_of_resultant_derivative_ne_zero (φ : R →+* K) (p : R[X])
    (hp : p.Monic) (hres : φ (p.resultant p.derivative) ≠ 0) : (p.map φ).Separable := by
  by_contra hsep
  apply hres
  rw [← resultant_derivative_map_of_monic φ p hp]
  apply Polynomial.resultant_eq_zero_iff.mpr
  exact ⟨Or.inl (hp.map φ).ne_zero, hsep⟩

end LeanCanny.CountingHierarchy
