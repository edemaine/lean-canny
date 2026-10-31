/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ClearedCoordinateCoefficients
public import LeanCanny.Algebra.IntegralRelativeCharacteristicBounds
public import LeanCanny.Algebra.IntegralReductionHeightBounds

/-! # Frozen spatial coefficient heights from original matrix bounds

Each original spatial monomial contributes a coefficient matrix, an
integer denominator power, and retained-height or denominator powers.
The original fixed-width spatial grid bounds the sum. Old parameter
monomials and their physical powers are never enumerated in the bound.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralFrozenCoefficientBounds
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralRelativeCharacteristicBounds
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] {M n dim : ℕ}

theorem element_power_height (b : Module.Basis (Fin M) ℤ A) (x : A) (H e E : ℕ)
    (h : ∀ r t, (Algebra.leftMulMatrix b x r t).natAbs ≤ 2 ^ H) (he : e ≤ E) (r t : Fin M) :
    (Algebra.leftMulMatrix b (x ^ e) r t).natAbs ≤ 2 ^ (E * (H + M.size)) := by
  rw [map_pow]
  exact (IntegralParameterMatrixBounds.pow_height _ H h e r t).trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ he))

def termHeight (n M W D C V Q : ℕ) : ℕ :=
  C + D * Q + n * (2 ^ W * (Q + V + M.size) + M.size) + 2 * M.size

theorem termHeight_binary {n M W D C V Q : List Bool → ℕ} (hn : BinaryFn n) (hM : BinaryFn M)
    (hW : UnaryFn W) (hD : BinaryFn D) (hC : BinaryFn C) (hV : BinaryFn V) (hQ : BinaryFn Q) :
    BinaryFn (fun c => termHeight (n c) (M c) (W c) (D c) (C c) (V c) (Q c)) :=
  ((hC.add (hD.mul hQ)).add
    (hn.mul (((BinaryFn.const 2).powUnary hW).mul ((hQ.add hV).add hM.size) |>.add hM.size))).add
      ((BinaryFn.const 2).mul hM.size)

theorem term_height (b : Module.Basis (Fin M) ℤ A) (q : ℤ) (height : ℕ → A)
    (offset dim D W C V Q : ℕ) (e : Fin n →₀ ℕ) (a : A)
    (he : ∀ i, e i < 2 ^ W) (ha : ∀ r t, (Algebra.leftMulMatrix b a r t).natAbs ≤ 2 ^ C)
    (hh : ∀ i : Fin n, ∀ r t, (Algebra.leftMulMatrix b (height i.val) r t).natAbs ≤ 2 ^ V)
    (hq : q.natAbs ≤ 2 ^ Q) (r t : Fin M) :
    (Algebra.leftMulMatrix b (ClearedCoordinateBlock.monomialScalar D (q : A) height offset dim e a) r t).natAbs ≤
      2 ^ termHeight n M W D C V Q := by
  have HQ : ∀ r t, (Algebra.leftMulMatrix b (q : A) r t).natAbs ≤ 2 ^ (Q + V) := fun r t =>
    (IntegralReductionHeightBounds.integer_entry_height b q Q hq r t).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  have HH (i : Fin n) : ∀ r t, (Algebra.leftMulMatrix b (height i.val) r t).natAbs ≤ 2 ^ (Q + V) := fun r t =>
    (hh i r t).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  have HA (i : Fin n) : ∀ r t,
      (Algebra.leftMulMatrix b (ClearedCoordinateBlock.scalarAtom (q : A) height offset dim i.val (e i)) r t).natAbs ≤
        2 ^ (2 ^ W * (Q + V + M.size)) := by
    intro r t
    unfold ClearedCoordinateBlock.scalarAtom
    split_ifs
    · exact element_power_height b (q : A) (Q + V) (e i) (2 ^ W) HQ (he i).le r t
    · exact element_power_height b (height i.val) (Q + V) (e i) (2 ^ W) (HH i) (he i).le r t
  have HP : ∀ r t, (Algebra.leftMulMatrix b
      (∏ i : Fin n, ClearedCoordinateBlock.scalarAtom (q : A) height offset dim i.val (e i)) r t).natAbs ≤
        2 ^ (n * (2 ^ W * (Q + V + M.size) + M.size)) := by
    intro r t
    simpa only [Finset.card_univ, Fintype.card_fin] using finset_product_height b Finset.univ
      (fun i : Fin n => ClearedCoordinateBlock.scalarAtom (q : A) height offset dim i.val (e i))
      (2 ^ W * (Q + V + M.size)) (fun i _ => HA i) r t
  have HZ : (q ^ (D - e.degree)).natAbs ≤ 2 ^ (D * Q) := by
    rw [Int.natAbs_pow]
    calc
      _ ≤ (2 ^ Q) ^ (D - e.degree) := Nat.pow_le_pow_left hq _
      _ = 2 ^ (Q * (D - e.degree)) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
        simpa only [Nat.mul_comm Q D] using Nat.mul_le_mul_left Q (Nat.sub_le D e.degree))
  have HZmatrix : ∀ r t, (Algebra.leftMulMatrix b ((q : A) ^ (D - e.degree)) r t).natAbs ≤ 2 ^ (D * Q) := by
    intro r t
    rw [← Int.cast_pow]
    exact IntegralReductionHeightBounds.integer_entry_height b _ _ HZ r t
  have HF := IntegralParameterMatrixBounds.mul_height (Algebra.leftMulMatrix b a)
    (Algebra.leftMulMatrix b ((q : A) ^ (D - e.degree))) C (D * Q) ha HZmatrix
  unfold ClearedCoordinateBlock.monomialScalar
  rw [map_mul, map_mul]
  have HE := IntegralParameterMatrixBounds.mul_height _ _ (C + D * Q + M.size)
    (n * (2 ^ W * (Q + V + M.size) + M.size)) HF HP r t
  convert HE using 1
  congr 1
  unfold termHeight
  ring

def coefficientHeight (n M W D C V Q : ℕ) : ℕ := termHeight n M W D C V Q + W * n

theorem coefficientHeight_binary {n M W D C V Q : List Bool → ℕ} (hn : BinaryFn n) (hM : BinaryFn M)
    (hW : UnaryFn W) (hD : BinaryFn D) (hC : BinaryFn C) (hV : BinaryFn V) (hQ : BinaryFn Q) :
    BinaryFn (fun c => coefficientHeight (n c) (M c) (W c) (D c) (C c) (V c) (Q c)) :=
  (termHeight_binary hn hM hW hD hC hV hQ).add ((BinaryFn.ofUnary hW).mul hn)

theorem coefficient_height (b : Module.Basis (Fin M) ℤ A) (q : ℤ) (height : ℕ → A)
    (offset dim D W C V Q : ℕ) (p : MvPolynomial (Fin n) A)
    (hs : ∀ e ∈ p.support, ∀ i, e i < 2 ^ W)
    (hc : ∀ e r t, (Algebra.leftMulMatrix b (p.coeff e) r t).natAbs ≤ 2 ^ C)
    (hh : ∀ i : Fin n, ∀ r t, (Algebra.leftMulMatrix b (height i.val) r t).natAbs ≤ 2 ^ V)
    (hq : q.natAbs ≤ 2 ^ Q) (m : Fin dim →₀ ℕ) (r t : Fin M) :
    (Algebra.leftMulMatrix b ((ClearedCoordinateBlock.specialize D (q : A) height offset dim p).coeff m) r t).natAbs ≤
      2 ^ coefficientHeight n M W D C V Q := by
  rw [ClearedCoordinateBlock.specialize_coefficient_grid W D (q : A) height offset dim p hs m, map_sum, Matrix.sum_apply]
  calc
    _ ≤ ∑ z : Fin (FixedWidthPolynomial.count n W),
        (Algebra.leftMulMatrix b (if ClearedCoordinateBlock.freeExponent offset dim (FixedWidthPolynomial.vector n W z) = m
          then ClearedCoordinateBlock.monomialScalar D (q : A) height offset dim (FixedWidthPolynomial.vector n W z)
            (p.coeff (FixedWidthPolynomial.vector n W z)) else 0) r t).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _z : Fin (FixedWidthPolynomial.count n W), 2 ^ termHeight n M W D C V Q := by
      apply Finset.sum_le_sum
      intro z _
      split_ifs
      · exact term_height b q height offset dim D W C V Q _ _ (FixedWidthPolynomial.vector_lt n W z)
          (hc _) hh hq r t
      · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
        exact Nat.zero_le _
    _ = FixedWidthPolynomial.count n W * 2 ^ termHeight n M W D C V Q := by simp
    _ = _ := by
      rw [FixedWidthPolynomial.count, ← pow_mul, ← pow_add]
      unfold coefficientHeight
      congr 1
      omega

end LeanCanny.Algebra.IntegralFrozenCoefficientBounds
