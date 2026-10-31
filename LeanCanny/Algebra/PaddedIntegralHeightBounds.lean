/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralInverseMatrixBounds
public import LeanCanny.Algebra.PaddedIntegralHeightMatrix

/-! # Derived coefficient heights for canonical padded scalar extensions

Original coefficient-matrix bounds control the constructed generator,
inverse matrix, numerator, and denominator. Advertised degrees may be
invalid and selected coefficients may be zero divisors. Every bound has
a native binary computation from the old rank and fixed scalar degree.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralParameterExtension
open IntegralCoordinateBasis FixedWidthPolynomial LeanCanny.Encoding
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] [Nontrivial A] {m B : ℕ}

def rootHeight (n N H : ℕ) : ℕ := N * (H + n.size)
def numeratorHeight (n N H : ℕ) : ℕ := rootHeight n N H + IntegralInverseMatrixBounds.height n H + (n * N).size

theorem numeratorHeight_linear (n N H : ℕ) :
    numeratorHeight n N H + 1 ≤ (N + 2 * n + 3) ^ 2 * (H + 1) := by
  have HB : numeratorHeight n N H + 1 ≤
      N * (H + n) + (n * n + n * (H + 1) + 1 + n * (H + n) + (n + 1)) + n * N + 1 := by
    unfold numeratorHeight rootHeight IntegralInverseMatrixBounds.height
      IntegralInverseMatrixBounds.polynomialHeight CharacteristicIntegerBounds.budget
    gcongr <;> exact Nat.size_le_self _
  have HC : 2 * n * N + 2 * n ^ 2 + 2 * n + 3 ≤ (N + 2 * n + 3) ^ 2 := by nlinarith
  have HD : N + 2 * n ≤ (N + 2 * n + 3) ^ 2 := by nlinarith
  calc
    _ ≤ (N + 2 * n) * H + (2 * n * N + 2 * n ^ 2 + 2 * n + 3) := by nlinarith [HB]
    _ ≤ (N + 2 * n + 3) ^ 2 * H + (N + 2 * n + 3) ^ 2 :=
      Nat.add_le_add (Nat.mul_le_mul_right H HD) HC
    _ = _ := by ring

theorem rootHeight_binary {n N H : List Bool → ℕ} (hn : BinaryFn n) (hN : BinaryFn N) (hH : BinaryFn H) :
    BinaryFn (fun c => rootHeight (n c) (N c) (H c)) := hN.mul (hH.add hn.size)

theorem numeratorHeight_binary {n N H : List Bool → ℕ} (hn : BinaryFn n) (hN : BinaryFn N) (hH : BinaryFn H) :
    BinaryFn (fun c => numeratorHeight (n c) (N c) (H c)) :=
  ((rootHeight_binary hn hN hH).add (IntegralInverseMatrixBounds.height_binary hn hH)).add (hn.mul hN).size

theorem root_height (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A) (d H : ℕ)
    (hp : ∀ k i j, (Algebra.leftMulMatrix b.finBasis (p.coeff k) i j).natAbs ≤ 2 ^ H)
    (i j : Fin (count (m + 1) B)) :
    (Algebra.leftMulMatrix (coordinateBasis b p d).finBasis (AdjoinRoot.root _) i j).natAbs ≤
      2 ^ rootHeight (count m B) (2 ^ B) H := by
  obtain ⟨⟨r, a⟩, rfl⟩ := (pairIndex m B).surjective i
  obtain ⟨⟨t, c⟩, rfl⟩ := (pairIndex m B).surjective j
  rw [fin_root_matrix]
  split_ifs with hcol hrow hdiag hpad
  · exact Nat.one_le_two_pow
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · rw [Int.natAbs_neg]
    have HK : a.val - (2 ^ B - d) < d := by have := a.isLt; omega
    apply (IntegralParameterMatrixBounds.normalized_height _ _ H d _ HK (hp _) (hp d) r t).trans
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hpad.1)
  · exact Nat.zero_le _

omit [Nontrivial A] in
theorem inverse_height (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A) (d H : ℕ)
    (hp : ∀ i j, (Algebra.leftMulMatrix b.finBasis (p.coeff d) i j).natAbs ≤ 2 ^ H)
    (i j : Fin (count m B)) : (inverseMatrix b p d i j).natAbs ≤ 2 ^ IntegralInverseMatrixBounds.height (count m B) H :=
  IntegralInverseMatrixBounds.inverse_height _ H hp i j

theorem lifted_inverse_height (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A) (d H : ℕ)
    (hp : ∀ i j, (Algebra.leftMulMatrix b.finBasis (p.coeff d) i j).natAbs ≤ 2 ^ H)
    (i j : Fin (count (m + 1) B)) :
    (Algebra.leftMulMatrix (coordinateBasis b p d).finBasis (AdjoinRoot.of _
      (Polynomial.aeval (p.coeff d) (IntegralParameterInverse.inverse (Algebra.leftMulMatrix b.finBasis (p.coeff d)).charpoly))) i j).natAbs ≤
      2 ^ IntegralInverseMatrixBounds.height (count m B) H := by
  obtain ⟨⟨r, a⟩, rfl⟩ := (pairIndex m B).surjective i
  obtain ⟨⟨t, c⟩, rfl⟩ := (pairIndex m B).surjective j
  rw [lifted_inverse_entry]
  split_ifs
  · exact inverse_height b p d H hp r t
  · exact Nat.zero_le _

theorem numerator_height (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A) (d H : ℕ)
    (hp : ∀ k i j, (Algebra.leftMulMatrix b.finBasis (p.coeff k) i j).natAbs ≤ 2 ^ H)
    (i j : Fin (count (m + 1) B)) :
    (Algebra.leftMulMatrix (coordinateBasis b p d).finBasis (numerator b p d) i j).natAbs ≤
      2 ^ numeratorHeight (count m B) (2 ^ B) H := by
  rw [numerator_matrix]
  have HM := IntegralParameterMatrixBounds.mul_height _ _ (rootHeight (count m B) (2 ^ B) H)
    (IntegralInverseMatrixBounds.height (count m B) H) (root_height b p d H hp)
    (lifted_inverse_height b p d H (hp d)) i j
  simpa only [numeratorHeight, count, pow_succ] using HM

omit [Nontrivial A] in
theorem denominator_height (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A) (d H : ℕ)
    (hp : ∀ i j, (Algebra.leftMulMatrix b.finBasis (p.coeff d) i j).natAbs ≤ 2 ^ H) :
    (denominator b p d).natAbs ≤ 2 ^ CharacteristicIntegerBounds.budget (count m B) H := by
  rw [denominator_finBasis]
  exact IntegralInverseMatrixBounds.denominator_height _ H hp

theorem numerator_coefficient_height (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A) (d H : ℕ)
    (hp : ∀ k i j, (Algebra.leftMulMatrix b.finBasis (p.coeff k) i j).natAbs ≤ 2 ^ H)
    (r : Fin (count (m + 1) B)) :
    ((numeratorPolynomial b p d).coeff (vector (m + 1) B r)).natAbs ≤
      2 ^ numeratorHeight (count m B) (2 ^ B) H := by
  change (((coordinateBasis b p d).representative (numerator b p d)).coeff _).natAbs ≤ _
  rw [(coordinateBasis b p d).coefficient_finMatrix]
  exact numerator_height b p d H hp r (zeroFin (m + 1) B)

end LeanCanny.Algebra.PaddedIntegralParameterExtension
