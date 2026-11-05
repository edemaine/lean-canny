/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SubtractiveCharacteristicSpace
public import LeanCanny.Algebra.RelativeMatrixDegree
/-! # Native characteristic coefficients for even full-box dimensions

The full fixed-width Macaulay box has even positive dimension. Its subtractive
determinant is therefore exactly the monic characteristic polynomial. The
original entry routine and its workspace remain charged.
-/
@[expose] public section
namespace LeanCanny.Algebra.EvenPolynomialCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

noncomputable def reader (N E : List Bool → ℕ)
    (A : (c : List Bool) → Matrix (Fin (N c)) (Fin (N c)) (Polynomial ℤ))
    (hN : ∀ c, 0 < N c) (hEven : ∀ c, Even (N c))
    (hn : BinaryFn N) (hE : BinaryFn E) (hA : ∀ c i j, (A c i j).natDegree ≤ E c)
    (source : List Bool → List Bool) (S : SpaceFunction source)
    (hc : ∀ c m (i j : Fin (N c)) u,
      source (pair (pair c m) (pair (BinaryNatCode.encode i.val)
        (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u)))) =
          residueBits ((((A c i j).coeff u) : ℤ) : ZMod (Nat.fromBitsLE m + 1))) :
    CertifiedPolynomial.BivariateReader (fun c => (A c).charpoly) := by
  let R := SubtractiveCharacteristicBits.reader N E A hN hn hE hA source S hc
  refine ⟨R.coefficient, R.evaluator, ?_⟩
  intro q u v
  rw [R.coefficient_eq, AffineCharacteristic.subtractive_det_eq_sign_mul_charpoly,
    Fintype.card_fin, (hEven _).neg_one_pow, Polynomial.C_1, one_mul]

theorem coefficient_degree (N E : List Bool → ℕ)
    (A : (c : List Bool) → Matrix (Fin (N c)) (Fin (N c)) (Polynomial ℤ))
    (hA : ∀ c i j, (A c i j).natDegree ≤ E c) (c : List Bool) (k : ℕ) :
    ((A c).charpoly.coeff k).natDegree ≤ N c * E c := by
  simpa only [Fintype.card_fin] using RelativeMatrixDegree.charpoly_coefficient (hA c) k

end LeanCanny.Algebra.EvenPolynomialCharacteristicBits
