/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MacaulayPaddedPolynomialValue
/-! # A normalized-value algorithm needing only the full native dimension

Using the full dimension for the padding exponent and quotient ceiling leaves
an additional power of `1-X` in the quotient. Its constant coefficient is one,
so coefficient zero is still the exact normalized universal value.
-/
@[expose] public section
namespace LeanCanny.Algebra.MacaulayFixedPaddedPolynomialValue
open Polynomial MvPolynomial
open scoped Classical
variable {n : ℕ} {R : Type*} [CommRing R]

theorem reduced_le_dimension (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hd : ∀ i, 0 < d i) (hW : Macaulay.level d < 2 ^ W) :
    MacaulayPaddedPolynomialValue.reduced d ≤ FixedWidthPolynomial.count (n + 1) W := by
  have HC := Macaulay.card_active_eq_extraneous_add d hd W hW
  have HA := Finset.card_le_univ (s := Macaulay.activeIndices d W)
  simp only [Fintype.card_fin] at HA
  unfold MacaulayPaddedPolynomialValue.reduced
  omega

noncomputable def quotient (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (d : Fin (n + 1) → ℕ) (W : ℕ) :=
  ScaledPolynomialQuotient.quotient (MacaulayPaddedPolynomialValue.divisor p d W)
    ((Macaulay.matrix p d W).charpoly * (1 - Polynomial.X) ^ FixedWidthPolynomial.count (n + 1) W)
    (FixedWidthPolynomial.count (n + 1) W) (FixedWidthPolynomial.count (n + 1) W)

section Domain
variable [IsDomain R]

theorem quotient_eq (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : Macaulay.level d < 2 ^ W) :
    quotient p d W = Macaulay.characteristicQuotient p d W *
      (1 - Polynomial.X) ^ (FixedWidthPolynomial.count (n + 1) W - MacaulayPaddedPolynomialValue.reduced d) := by
  let N := FixedWidthPolynomial.count (n + 1) W
  let r := MacaulayPaddedPolynomialValue.reduced d
  have HR : r ≤ N := reduced_le_dimension d W hd hW
  have HF : (Macaulay.matrix p d W).charpoly * (1 - Polynomial.X) ^ N =
      MacaulayPaddedPolynomialValue.divisor p d W *
        (Macaulay.characteristicQuotient p d W * (1 - Polynomial.X) ^ (N - r)) := by
    have HE : N = r + (N - r) := (Nat.add_sub_of_le HR).symm
    conv_lhs => rw [HE, pow_add, ← mul_assoc]
    change MacaulayPaddedPolynomialValue.dividend p d W * _ = _
    rw [MacaulayPaddedPolynomialValue.factorization p d W hp hd hW]
    simp only [mul_assoc]
  have HD : (MacaulayPaddedPolynomialValue.divisor p d W).natDegree = N := by
    simpa only [MacaulayPaddedPolynomialValue.divisor, Fintype.card_fin] using
      Matrix.charpoly_natDegree_eq_dim (Macaulay.extraneousPadded p d W)
  have HL : (MacaulayPaddedPolynomialValue.divisor p d W).coeff N = 1 := by
    have H := (Matrix.charpoly_monic (Macaulay.extraneousPadded p d W)).leadingCoeff
    change (MacaulayPaddedPolynomialValue.divisor p d W).coeff
      (MacaulayPaddedPolynomialValue.divisor p d W).natDegree = 1 at H
    exact (congrArg (MacaulayPaddedPolynomialValue.divisor p d W).coeff HD).symm.trans H
  have HQ : (Macaulay.characteristicQuotient p d W * (1 - Polynomial.X) ^ (N - r)).natDegree ≤ N := by
    apply Polynomial.natDegree_mul_le.trans
    apply (Nat.add_le_add (le_of_eq (Macaulay.characteristicQuotient_natDegree p d W hd hW))
      ((Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left _ (show (1 - Polynomial.X : Polynomial R).natDegree ≤ 1 by compute_degree)))).trans
    simp only [Nat.mul_one]
    exact Nat.add_sub_of_le HR |>.le
  rw [quotient, HF, ScaledPolynomialQuotient.quotient_mul _ _ _ _ HD.le HQ, HL,
    one_pow, Polynomial.C_1, one_mul]

theorem value_eq_coefficient_zero (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) :
    MacaulayUniversal.polynomialValue d W hdegree hW p = (quotient p d W).coeff 0 := by
  have HP (k : ℕ) : ((1 - Polynomial.X : Polynomial R) ^ k).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow]
    simp
  rw [quotient_eq p d W hp hd hW, Polynomial.mul_coeff_zero, HP, mul_one,
    MacaulayUniversal.polynomialValue_eq_eval_zero d W hdegree hW p hp hd,
    ← Polynomial.coeff_zero_eq_eval_zero]

end Domain
end LeanCanny.Algebra.MacaulayFixedPaddedPolynomialValue
