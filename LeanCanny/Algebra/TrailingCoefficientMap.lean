/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.InfinitesimalSign
/-! # Lowest coefficients commute with a specialization when that coefficient survives -/
@[expose] public section
namespace LeanCanny.Algebra
open Polynomial
open scoped Classical

theorem trailingCoeff_map_of_survives {R S : Type*} [Semiring R] [Semiring S]
    (φ : R →+* S) (p : Polynomial R) (h : φ p.trailingCoeff≠0) :
    (p.map φ).trailingCoeff=φ p.trailingCoeff := by
  have HC : (p.map φ).coeff p.natTrailingDegree≠0 := by
    simpa only [Polynomial.coeff_map,Polynomial.trailingCoeff] using h
  have HP : p.map φ≠0 := by
    intro HZ
    exact HC (by rw [HZ,Polynomial.coeff_zero])
  have HD : (p.map φ).natTrailingDegree=p.natTrailingDegree := le_antisymm
    (Polynomial.natTrailingDegree_le_of_ne_zero HC)
    (Polynomial.le_natTrailingDegree HP (fun m hm => by
      rw [Polynomial.coeff_map,Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hm,map_zero]))
  simp only [Polynomial.trailingCoeff,HD,Polynomial.coeff_map]

end LeanCanny.Algebra
