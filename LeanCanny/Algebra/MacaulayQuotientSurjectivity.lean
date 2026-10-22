/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayMaximalMinors
public import LeanCanny.Algebra.MatrixMaximalMinorSpan
public import LeanCanny.Algebra.MacaulayIdealImage

/-! # Surjective full Macaulay matrices have unit polynomial quotient

The quotient divides every maximal minor over every commutative ring.
Surjectivity supplies a right section, so the quotient divides one. Over
a nontrivial ring it is nonzero, without any condition on the extraneous
determinant. Ideal membership of every form at the Macaulay level gives
the same conclusion through the proved row-image equivalence.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem polynomialValue_isUnit_of_fullMatrix_surjective (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hsurj : Function.Surjective (fun v => Matrix.vecMul v (Macaulay.fullMatrix p d W))) :
    IsUnit (polynomialValue d W hdegree hW p) :=
  MatrixMaximalMinorSpan.isUnit_of_dvd_maximal_minors_of_surjective (Macaulay.fullMatrix p d W) _
    (polynomialValue_dvd_fullMinor d W hdegree hW p hp hd) hsurj

theorem polynomialValue_ne_zero_of_fullMatrix_surjective [Nontrivial R] (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hsurj : Function.Surjective (fun v => Matrix.vecMul v (Macaulay.fullMatrix p d W))) :
    polynomialValue d W hdegree hW p ≠ 0 :=
  (polynomialValue_isUnit_of_fullMatrix_surjective d W hdegree hW p hp hd hsurj).ne_zero

theorem polynomialValue_isUnit_of_homogeneous_membership (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hmem : ∀ f : MvPolynomial (Fin (n + 1)) R, f.IsHomogeneous (Macaulay.level d) → f ∈ ProjectiveNullstellensatz.generated p) :
    IsUnit (polynomialValue d W hdegree hW p) :=
  polynomialValue_isUnit_of_fullMatrix_surjective d W hdegree hW p hp hd
    ((Macaulay.fullMatrix_surjective_iff_homogeneous_membership p d W hp hW).mpr hmem)

end LeanCanny.Algebra.MacaulayUniversal
