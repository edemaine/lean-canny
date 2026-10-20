/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayReducedCount
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.FieldTheory.RatFunc.Degree

/-! # The degree of the Macaulay characteristic determinant quotient

Both subtractive characteristic determinants have their full matrix degree.
After embedding the coefficient domain in a field, the rational quotient has
integer degree equal to the reduced-monomial count. Polynomiality is separate.
-/

@[expose] public section

namespace LeanCanny.Algebra
open scoped BigOperators
namespace AffineCharacteristic
variable {R ι : Type*} [CommRing R] [IsDomain R] [Fintype ι] [DecidableEq ι]

theorem subtractive_det_ne_zero (A : Matrix ι ι R) : (subtractiveMatrix A).det ≠ 0 := by
  rw [subtractive_det_eq_charpoly]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) A.charpoly_monic.ne_zero

theorem subtractive_det_natDegree (A : Matrix ι ι R) : (subtractiveMatrix A).det.natDegree = Fintype.card ι := by
  rw [subtractive_det_eq_charpoly, Polynomial.natDegree_mul
    (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) A.charpoly_monic.ne_zero]
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_neg, Polynomial.natDegree_one,
    mul_zero, zero_add, Matrix.charpoly_natDegree_eq_dim]

end AffineCharacteristic

namespace PolynomialQuotientDegree
variable {R K : Type*} [CommRing R] [Field K]

theorem intDegree_map (φ : R →+* K) (hφ : Function.Injective φ) (p q : Polynomial R) (hp : p ≠ 0) (hq : q ≠ 0) :
    (RatFunc.mk (p.map φ) (q.map φ)).intDegree = (p.natDegree : ℤ) - q.natDegree := by
  have hp' : p.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hφ).mpr hp
  have hq' : q.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hφ).mpr hq
  rw [RatFunc.mk_eq_div, RatFunc.intDegree_div (RatFunc.algebraMap_ne_zero hp') (RatFunc.algebraMap_ne_zero hq'),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial,
    Polynomial.natDegree_map_eq_of_injective hφ, Polynomial.natDegree_map_eq_of_injective hφ]

variable [IsDomain R]

noncomputable def coefficientExtension (φ : R →+* K) (hφ : Function.Injective φ) : RatFunc R →+* RatFunc K :=
  RatFunc.mapRingHom (Polynomial.mapRingHom φ)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (Polynomial.map_injective _ hφ))

theorem coefficientExtension_injective (φ : R →+* K) (hφ : Function.Injective φ) :
    Function.Injective (coefficientExtension φ hφ) :=
  RatFunc.map_injective (Polynomial.mapRingHom φ)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (Polynomial.map_injective _ hφ))
    (Polynomial.map_injective _ hφ)

theorem coefficientExtension_mk (φ : R →+* K) (hφ : Function.Injective φ) (p q : Polynomial R) :
    coefficientExtension φ hφ (RatFunc.mk p q) = RatFunc.mk (p.map φ) (q.map φ) := by
  rw [RatFunc.mk_eq_div, RatFunc.mk_eq_div]
  exact RatFunc.map_apply_div (Polynomial.mapRingHom φ)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (Polynomial.map_injective _ hφ)) p q

end PolynomialQuotientDegree

namespace Macaulay
variable {n : ℕ} {R K : Type*} [CommRing R] [IsDomain R] [Field K]

theorem characteristicQuotient_intDegree (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i) (W : ℕ) (hW : level d < 2 ^ W) (φ : R →+* K) (hφ : Function.Injective φ) :
    (RatFunc.mk ((activeCharacteristic p d W).map φ)
      ((AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W)).det.map φ)).intDegree =
        ∑ i, ∏ j ∈ Finset.univ.erase i, d j := by
  unfold activeCharacteristic
  rw [PolynomialQuotientDegree.intDegree_map φ hφ _ _
    (AffineCharacteristic.subtractive_det_ne_zero (activeMinor p d W))
    (AffineCharacteristic.subtractive_det_ne_zero (extraneousMinor p d W))]
  rw [AffineCharacteristic.subtractive_det_natDegree, AffineCharacteristic.subtractive_det_natDegree]
  simp only [Fintype.card_coe]
  have hc := card_active_eq_extraneous_add d hd W hW
  omega

end Macaulay
end LeanCanny.Algebra
