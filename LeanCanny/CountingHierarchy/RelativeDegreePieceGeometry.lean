/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RelativeFiberSeparation
public import LeanCanny.CountingHierarchy.DegreePiecePolynomial

/-! # Actual polynomial degree pieces carry clopen good and bad fibers -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Polynomial Set
open scoped Topology Classical

attribute [local irreducible] finiteRelativeSection finiteRelativeCharacteristic
  relativeCharacteristic relativeBivariate specializedRelativeSection firstVariableCoefficient

variable {n m : ℕ}

theorem specializedRelativeSection_coeff (d : ℕ) (P : MvPolynomial (Fin (n + m)) ℤ)
    (hP : P.totalDegree ≤ d + 1) (x : Fin m → ℝ) (j : ℕ) :
    (specializedRelativeSection d P hP x).coeff j =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) x (firstVariableCoefficient (finiteRelativeSection d P hP) j) := by
  rw [specializedRelativeSection, Polynomial.coeff_map]
  rw [firstVariableCoefficient]
  rfl

theorem specializedRelativeSection_degree_le (d : ℕ) (P : MvPolynomial (Fin (n + m)) ℤ)
    (hP : P.totalDegree ≤ d + 1) (x : Fin m → ℝ) :
    (specializedRelativeSection d P hP x).natDegree ≤ (finiteRelativeSection d P hP).totalDegree := by
  rw [specializedRelativeSection]
  exact Polynomial.natDegree_map_le.trans ((MvPolynomial.natDegree_finSuccEquiv _).le.trans
    (MvPolynomial.degreeOf_le_totalDegree _ _))

theorem relative_good_isClopen_on_degreePiece (d : ℕ) (hd : 1 ≤ d) (he : Even (d + 2))
    (P : MvPolynomial (Fin (n + m)) ℤ) (hP : P.totalDegree ≤ d + 1)
    (hFn : ∀ x z, 0 ≤ MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) P)
    (N : ℕ) (hN : (finiteRelativeSection d P hP).totalDegree ≤ N) (k : Fin (N + 1)) :
    IsClopen {x : degreePiece
      (fun j : Fin (N + 1) => fun x : Fin m → ℝ =>
        MvPolynomial.eval₂ (Int.castRingHom ℝ) x (firstVariableCoefficient (finiteRelativeSection d P hP) j.val)) k |
      ¬∃ z : Fin n → ℝ, MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x.val) P = 0} := by
  let a : Fin (N + 1) → (Fin m → ℝ) → ℝ := fun j x =>
    MvPolynomial.eval₂ (Int.castRingHom ℝ) x (firstVariableCoefficient (finiteRelativeSection d P hP) j.val)
  let S := degreePiece a k
  change IsClopen {x : S | ¬∃ z : Fin n → ℝ,
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x.val) P = 0}
  apply relative_emptyFibers_isClopen (A := S) d hd he P hP (fun x : S => x.val) continuous_subtype_val
    (fun x z => hFn x.val z) k.val
  · intro x
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    by_cases hjN : j < N + 1
    · rw [specializedRelativeSection_coeff]
      exact x.property.2 ⟨j, hjN⟩ hj
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        ((specializedRelativeSection_degree_le d P hP x.val).trans_lt (by omega))
  · intro x
    rw [specializedRelativeSection_coeff]
    exact x.property.1

end LeanCanny.CountingHierarchy
