/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedUniformVirtualInputs
public import LeanCanny.Algebra.IntegralMixedVirtualOriginalRows
public import LeanCanny.Algebra.IntegralMixedVirtualNativeAccess

/-! # Actual full original-row heights from the retained bank

The original low and gradient estimates include denominator clearing.
Integer Fermat terms are restored with derived scalar bounds. Their sum
gives every actual original test-row coefficient matrix a native budget,
without an extra test-row or Gram height premise.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualOriginalRowBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource IntegralMixedCoordinateBounds
open IntegralMixedVirtualSweepSource IntegralMixedVirtualOriginalRows
open scoped Classical BigOperators

noncomputable def lowHeight (F : Family) (I : Indices F) (H : OriginalBounds F) : List Bool → ℕ :=
  IntegralOriginalCriticalBounds.sourceBudget (source F I) (IntegralMixedUniformVirtualInputs.inputs F I H)

noncomputable def gradientHeight (F : Family) (I : Indices F) (H : OriginalBounds F) : List Bool → ℕ :=
  IntegralOriginalCriticalBounds.gradientBudget (source F I) (IntegralMixedUniformVirtualInputs.inputs F I H)

def scalarHeight (F : Family) (H : OriginalBounds F) (q : List Bool) : ℕ :=
  IntegralMixedUniformVirtualInputs.height F H q +
    (F.spatial q).degree * IntegralMixedUniformVirtualInputs.height F H q

noncomputable def height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool) : ℕ :=
  lowHeight F I H q + gradientHeight F I H q + scalarHeight F H q + (F.spatial q).degree.size +
    (F.ambient q - (F.rule q).critical.offset.val + 1).size + 1

theorem frozen_height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool)
    (e : Fin (F.ambient q - (F.rule q).critical.offset.val + 1) →₀ ℕ)
    (u v : Fin (count (F.birth q + 1) (F.width q))) :
    (Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      ((frozen F I q).coeff e) u v).natAbs ≤ 2 ^ lowHeight F I H q := by
  let read (p : MvPolynomial (Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) (Coefficient F q)) : ℕ :=
    (Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis (p.coeff e) u v).natAbs
  have HE : read ((source F I).toEuler.toGradient.toFrozen.lowerPolynomial q) ≤ 2 ^ lowHeight F I H q :=
    IntegralOriginalCriticalBounds.source_height (source F I) (IntegralMixedUniformVirtualInputs.inputs F I H) q e u v
  exact HE

theorem gradient_height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (e : Fin (F.ambient q - (F.rule q).critical.offset.val + 1) →₀ ℕ)
    (u v : Fin (count (F.birth q + 1) (F.width q))) :
    (Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      ((gradient F I q j).coeff e) u v).natAbs ≤ 2 ^ gradientHeight F I H q := by
  let read (p : MvPolynomial (Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) (Coefficient F q)) : ℕ :=
    (Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis (p.coeff e) u v).natAbs
  have HE : read (IntegralCriticalGradientBits.polynomial (source F I).toEuler.toGradient q j) ≤
      2 ^ gradientHeight F I H q :=
    IntegralOriginalCriticalBounds.gradient_height (source F I) (IntegralMixedUniformVirtualInputs.inputs F I H) q j e u v
  exact HE

theorem scalar_height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool) :
    (originalScale F q).natAbs ≤ 2 ^ scalarHeight F H q := by
  have HA := (IntegralMixedUniformVirtualInputs.inputs F I H).leading q
  have HQ := (IntegralMixedUniformVirtualInputs.inputs F I H).denominator q
  change (F.spatial q).leading.natAbs ≤ 2 ^ IntegralMixedUniformVirtualInputs.height F H q at HA
  change (denominator F q).natAbs ≤ 2 ^ IntegralMixedUniformVirtualInputs.height F H q at HQ
  unfold originalScale scalarHeight
  rw [Int.natAbs_mul, Int.natAbs_pow, pow_add]
  apply Nat.mul_le_mul HA
  exact (Nat.pow_le_pow_left HQ _).trans_eq (by rw [← pow_mul, Nat.mul_comm])

theorem derivative_scalar_height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool) :
    (originalScale F q * (F.spatial q).degree : ℤ).natAbs ≤ 2 ^ (scalarHeight F H q + (F.spatial q).degree.size) := by
  rw [Int.natAbs_mul, Int.natAbs_natCast, pow_add]
  exact Nat.mul_le_mul (scalar_height F I H q) (Nat.lt_size_self _).le

theorem coefficient_height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (e : Fin (F.ambient q - (F.rule q).critical.offset.val + 1) →₀ ℕ)
    (u v : Fin (count (F.birth q + 1) (F.width q))) :
    (Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      ((row F q j).coeff e) u v).natAbs ≤ 2 ^ height F I H q := by
  let b := (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
  have HS := scalar_height F I H q
  by_cases Hj : j = objective (F.rule q)
  · rw [equation_coefficient F I q j Hj e, map_add, Matrix.add_apply]
    have HM : Algebra.leftMulMatrix b
        ((originalScale F q : Coefficient F q) * ∑ k, if Finsupp.single k (F.spatial q).degree = e then 1 else 0) u v =
        ∑ k, if Finsupp.single k (F.spatial q).degree = e then
          Algebra.leftMulMatrix b (originalScale F q : Coefficient F q) u v else 0 := by
      rw [Finset.mul_sum, map_sum, Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp only [mul_one, mul_zero, map_zero, Matrix.zero_apply]
    have HB : (Algebra.leftMulMatrix b
        ((originalScale F q : Coefficient F q) * ∑ k, if Finsupp.single k (F.spatial q).degree = e then 1 else 0) u v).natAbs ≤
        2 ^ (scalarHeight F H q + (F.ambient q - (F.rule q).critical.offset.val + 1).size) := by
      rw [HM]
      calc
        _ ≤ ∑ k, (if Finsupp.single k (F.spatial q).degree = e then
            Algebra.leftMulMatrix b (originalScale F q : Coefficient F q) u v else 0).natAbs := Int.natAbs_sum_le _ _
        _ ≤ ∑ _k : Fin (F.ambient q - (F.rule q).critical.offset.val + 1), 2 ^ scalarHeight F H q := by
          apply Finset.sum_le_sum
          intro k _
          split_ifs
          · exact IntegralHistoryCriticalBits.integer_entry_height b _ _ HS u v
          · exact Nat.zero_le _
        _ = (F.ambient q - (F.rule q).critical.offset.val + 1) * 2 ^ scalarHeight F H q := by simp
        _ ≤ 2 ^ (F.ambient q - (F.rule q).critical.offset.val + 1).size * 2 ^ scalarHeight F H q :=
          Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
        _ = _ := by rw [← pow_add, Nat.add_comm]
    exact (IntegralFrozenConstantBounds.add_bound _ _ _ _ (frozen_height F I H q e u v) HB).trans
      (Nat.pow_le_pow_right (by decide) (by unfold height; omega))
  · rw [derivative_coefficient F I q j Hj e, map_add, Matrix.add_apply]
    have HB : (Algebra.leftMulMatrix b
        (if Finsupp.single j ((F.spatial q).degree - 1) = e then
          ((originalScale F q * (F.spatial q).degree : ℤ) : Coefficient F q) else 0) u v).natAbs ≤
          2 ^ (scalarHeight F H q + (F.spatial q).degree.size) := by
      split_ifs
      · exact IntegralHistoryCriticalBits.integer_entry_height b _ _ (derivative_scalar_height F I H q) u v
      · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
        exact Nat.zero_le _
    exact (IntegralFrozenConstantBounds.add_bound _ _ _ _ (gradient_height F I H q j e u v) HB).trans
      (Nat.pow_le_pow_right (by decide) (by unfold height; omega))

theorem height_binary (F : Family) (I : Indices F) (H : OriginalBounds F)
    (h : IntegralMixedVirtualNativeBits.Metadata F I)
    (hS : BinaryFn F.cap) (hL : BinaryFn H.nodes) (hG : BinaryFn H.bankHeight) : BinaryFn (height F I H) := by
  have HT := IntegralMixedUniformVirtualInputs.height_binary F H h.ambient hS hL hG
  have HL := IntegralOriginalCriticalBounds.sourceBudget_binary (source F I) (IntegralMixedUniformVirtualInputs.inputs F I H)
    (IntegralMixedVirtualNativeBits.criticalAccess F I h) HT HT HT HT
  have HD := IntegralOriginalCriticalBounds.gradientBudget_binary (source F I) (IntegralMixedUniformVirtualInputs.inputs F I H)
    (IntegralMixedVirtualNativeBits.criticalAccess F I h) HT HT HT
  exact ((((HL.add HD).add (HT.add (h.degree.mul HT))).add h.degree.size).add
    (BinaryFn.ofUnary (IntegralMixedVirtualNativeBits.free_unary F I h)).size).add (BinaryFn.const 1)

end LeanCanny.Algebra.IntegralMixedVirtualOriginalRowBounds
