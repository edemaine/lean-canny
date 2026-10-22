/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayKoszulRelations
public import LeanCanny.Algebra.MacaulaySubtractiveSystem

/-! # Nonzero Koszul relations for the characteristic-shifted system

The shift preserves spatial homogeneity. Each shifted polynomial is nonzero
because its designated coordinate-power coefficient has characteristic
coefficient -1. Compatible pairs therefore give nonzero finite kernel vectors
for the full graded multiplication matrix, even when original inputs vanish.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped Classical
variable {n : ℕ} {R : Type*} [CommRing R]

theorem subtractiveSystem_homogeneous (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (i : Fin n) :
    (subtractiveSystem p d i).IsHomogeneous (d i) := by
  exact ((hp i).map Polynomial.C).sub
    (MvPolynomial.isHomogeneous_monomial Polynomial.X (Finsupp.degree_single i (d i)))

theorem subtractiveSystem_ne_zero [Nontrivial R] (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (i : Fin n) :
    subtractiveSystem p d i ≠ 0 := by
  have hc : ((subtractiveSystem p d i).coeff (Finsupp.single i (d i))).coeff 1 = (-1 : R) := by
    simp [subtractiveSystem, MvPolynomial.coeff_map]
  intro hz
  apply (neg_ne_zero.mpr (one_ne_zero : (1 : R) ≠ 0))
  rw [← hc, hz]
  simp

theorem subtractive_koszul_vecMul_eq_zero (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ k, (p k).IsHomogeneous (d k)) (hW : level d < 2 ^ W)
    (i j : Fin n) (hij : i ≠ j) (m : Fin n →₀ ℕ) (hm : m.degree + d i + d j = level d) :
    Matrix.vecMul (sourceCoefficients (koszulMultipliers (subtractiveSystem p d) i j m) d W)
      (fullMatrix (subtractiveSystem p d) d W) = 0 :=
  koszul_vecMul_eq_zero _ d W (subtractiveSystem_homogeneous p d hp) hW i j hij m hm

theorem subtractive_koszul_coefficients_ne_zero [IsDomain R]
    (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ k, (p k).IsHomogeneous (d k)) (hW : level d < 2 ^ W)
    (i j : Fin n) (hij : i ≠ j) (m : Fin n →₀ ℕ) (hm : m.degree + d i + d j = level d) :
    sourceCoefficients (koszulMultipliers (subtractiveSystem p d) i j m) d W ≠ 0 :=
  koszul_coefficients_ne_zero _ d W (subtractiveSystem_homogeneous p d hp) hW i j hij m hm
    (subtractiveSystem_ne_zero p d j)

end LeanCanny.Algebra.Macaulay
