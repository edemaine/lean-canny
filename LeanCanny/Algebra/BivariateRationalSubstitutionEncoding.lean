/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BivariateRationalSubstitutionBounds
public import LeanCanny.Algebra.IndexedRationalSubstitution

/-! # Kronecker encoding after multivariate denominator clearing

The source has integer coefficients. Its parameter coordinate is an ordinary
variable, so encoding the already-formed rational coordinates commutes with
clearing. No symbolic leaf degree or primitive preparation is recomputed.
-/

@[expose] public section
namespace LeanCanny.Algebra.BivariateRationalSubstitution
open Polynomial
open scoped Classical

variable {σ : Type*} [Fintype σ]

theorem encode_clearedWith (B : ℕ) (D : σ → ℕ) (p : MvPolynomial σ ℤ)
    (n d : σ → (ℤ[X])[X]) :
    PolynomialKronecker.encode B (RationalSubstitution.clearedWith D (p.map (Int.castRingHom ℤ[X])) n d) =
      RationalSubstitution.clearedWith D p
        (fun i => PolynomialKronecker.encode B (n i)) (fun i => PolynomialKronecker.encode B (d i)) := by
  unfold RationalSubstitution.clearedWith
  rw [MvPolynomial.support_map_of_injective _ (show Function.Injective (Int.castRingHom ℤ[X]) from Polynomial.C_injective)]
  simp only [map_sum, map_mul, map_prod, map_pow, PolynomialKronecker.encode_C, MvPolynomial.coeff_map]
  rfl

theorem coefficient_clearedWith (B : ℕ) (D : σ → ℕ) (p : MvPolynomial σ ℤ)
    (n d : σ → (ℤ[X])[X])
    (hB : ∀ j, ((RationalSubstitution.clearedWith D (p.map (Int.castRingHom ℤ[X])) n d).coeff j).natDegree < B)
    (i j : ℕ) (hi : i < B) :
    (RationalSubstitution.clearedWith D p
      (fun a => PolynomialKronecker.encode B (n a)) (fun a => PolynomialKronecker.encode B (d a))).coeff (i + B * j) =
      ((RationalSubstitution.clearedWith D (p.map (Int.castRingHom ℤ[X])) n d).coeff j).coeff i := by
  rw [← encode_clearedWith]
  exact PolynomialKronecker.coefficient B _ hB i j hi

end LeanCanny.Algebra.BivariateRationalSubstitution
