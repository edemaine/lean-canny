/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SeparatedCriticalPolynomial

/-! # Specializing the actual deformation and its critical equations -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial
open scoped Classical

variable {S T : Type*} [CommRing S] [CommRing T] {n : ℕ}

theorem potentialPolynomial_map (φ : S →+* T) (ell : ℕ) (a : Fin n → S) :
    (potentialPolynomial ell a).map φ = potentialPolynomial ell (fun i => φ (a i)) := by
  simp only [potentialPolynomial, map_sum, map_add, map_sub, map_mul, map_pow, map_X,
    map_C, map_natCast]

theorem criticalLower_map (φ : S →+* T) (ell : ℕ) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (i : Fin n) :
    (criticalLower ell a u F i).map φ =
      criticalLower ell (fun i => φ (a i)) (φ u) (F.map φ) i := by
  simp only [criticalLower, map_sub, map_mul, map_C, map_pow, pderiv_map]

theorem deformedPolynomial_map (φ : S →+* T) (ell : ℕ) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) :
    (deformedPolynomial ell a u F).map φ =
      deformedPolynomial ell (fun i => φ (a i)) (φ u) (F.map φ) := by
  simp only [deformedPolynomial, map_add, potentialPolynomial_map, map_mul, map_C, map_natCast]

end LeanCanny.CountingHierarchy
