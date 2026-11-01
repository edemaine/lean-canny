/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralActionHeightBounds
public import LeanCanny.Algebra.PrincipalSubresultant.Basic

/-! # Multiplication-matrix bounds for literal principal determinants

Formal degree bounds control the integer derivative multiplier. Every
principal matrix entry is a coefficient of the polynomial or derivative;
the resulting determinant bound uses only that formal degree and the
coefficient-algebra rank. Zero divisors require no extra hypothesis.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralPrincipalHeightBounds
open LeanCanny.Encoding LeanCanny.Computation Polynomial PrincipalSubresultant
open scoped Classical
variable {A : Type*} [CommRing A] {M : ℕ}

theorem derivative_height (b : Module.Basis (Fin M) ℤ A) (p : Polynomial A) (D H : ℕ)
    (hD : p.natDegree ≤ D)
    (hH : ∀ k r t, (Algebra.leftMulMatrix b (p.coeff k) r t).natAbs ≤ 2 ^ H)
    (k : ℕ) (r t : Fin M) :
    (Algebra.leftMulMatrix b (p.derivative.coeff k) r t).natAbs ≤ 2 ^ (H + D.size) := by
  rw [Polynomial.coeff_derivative]
  by_cases HK : k + 1 ≤ D
  · rw [mul_comm, show (k : A) + 1 = (((k + 1 : ℕ) : ℤ) : A) from by simp,
      IntegralActionHeightBounds.int_multiply_entry, Int.natAbs_mul, Int.natAbs_natCast, pow_add]
    exact (Nat.mul_le_mul (HK.trans (Nat.lt_size_self _).le) (hH _ r t)).trans_eq (Nat.mul_comm _ _)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hD.trans_lt (by omega)), zero_mul,
      map_zero, Matrix.zero_apply, Int.natAbs_zero]
    exact Nat.zero_le _

theorem matrix_height (b : Module.Basis (Fin M) ℤ A) (p q : Polynomial A) (m n j H : ℕ)
    (hp : ∀ k r t, (Algebra.leftMulMatrix b (p.coeff k) r t).natAbs ≤ 2 ^ H)
    (hq : ∀ k r t, (Algebra.leftMulMatrix b (q.coeff k) r t).natAbs ≤ 2 ^ H)
    (i k : Fin ((m - j) + (n - j))) (r t : Fin M) :
    (Algebra.leftMulMatrix b (subresultantMatrix p q m n j i k) r t).natAbs ≤ 2 ^ H := by
  induction k using Fin.addCases with
  | left k =>
    rw [subresultantMatrix_castAdd]
    split_ifs
    · exact hq _ r t
    · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
      exact Nat.zero_le _
  | right k =>
    rw [subresultantMatrix_natAdd]
    split_ifs
    · exact hp _ r t
    · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
      exact Nat.zero_le _

def height (D M H : ℕ) : ℕ :=
  H + IntegralRelativeCharacteristicBounds.determinantHeight (2 * D) M (H + D.size) + M.size

theorem height_mono {D E M R H G : ℕ} (hD : D ≤ E) (hM : M ≤ R) (hH : H ≤ G) :
    height D M H ≤ height E R G := by
  unfold height IntegralRelativeCharacteristicBounds.determinantHeight
  gcongr <;> exact Nat.size_le_size (by omega)

theorem height_binary {D M H : List Bool → ℕ} (hD : BinaryFn D) (hM : BinaryFn M) (hH : BinaryFn H) :
    BinaryFn (fun q => height (D q) (M q) (H q)) :=
  (hH.add (IntegralRelativeCharacteristicBounds.determinantHeight_binary
    ((BinaryFn.const 2).mul hD) hM (hH.add hD.size))).add hM.size

theorem principal_height (b : Module.Basis (Fin M) ℤ A) (p : Polynomial A) (D H j : ℕ)
    (hD : p.natDegree ≤ D)
    (hH : ∀ k r t, (Algebra.leftMulMatrix b (p.coeff k) r t).natAbs ≤ 2 ^ H)
    (r t : Fin M) :
    (Algebra.leftMulMatrix b (p.coeff D * psc p p.derivative D (D - 1) j) r t).natAbs ≤
      2 ^ height D M H := by
  have HP (k : ℕ) (u v : Fin M) :
      (Algebra.leftMulMatrix b (p.coeff k) u v).natAbs ≤ 2 ^ (H + D.size) :=
    (hH k u v).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  have HD := IntegralRelativeCharacteristicBounds.determinant_height b
    (subresultantMatrix p p.derivative D (D - 1) j) (H + D.size)
    (matrix_height b p p.derivative D (D - 1) j (H + D.size) HP (derivative_height b p D H hD hH))
  have Hsize : (D - j) + (D - 1 - j) ≤ 2 * D := by omega
  have Hdet (u v : Fin M) :
      (Algebra.leftMulMatrix b (psc p p.derivative D (D - 1) j) u v).natAbs ≤
        2 ^ IntegralRelativeCharacteristicBounds.determinantHeight (2 * D) M (H + D.size) := by
    rw [psc_def]
    exact (HD u v).trans (Nat.pow_le_pow_right (by decide)
      (IntegralRelativeCharacteristicBounds.determinantHeight_mono (by simpa using Hsize) M (H + D.size)))
  rw [map_mul]
  exact IntegralParameterMatrixBounds.mul_height _ _ H _ (hH D) Hdet r t

end LeanCanny.Algebra.IntegralPrincipalHeightBounds
