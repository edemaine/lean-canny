/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralClearedCriticalSpace
public import LeanCanny.Algebra.IntegralActionHeightBounds
public import LeanCanny.Algebra.IntegralReductionHeightBounds

/-! # Native linear height budgets for the constructed critical annihilator

Bounds on the actual Euler lower coefficients and common integer leading
coefficient bound the constructed reduction, action, characteristic
coefficients, and scalar rescaling. The binary budget is linear in these
input heights, with a factor depending on spatial size and old rank.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralClearedCriticalBounds
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralClearedCriticalBits
set_option backward.isDefEq.respectTransparency false

noncomputable def commonLeading (S : Source) (c : List Bool) : ℤ :=
  S.leading c * S.denominator c ^ S.allowance c * (S.allowance c : ℤ)

structure Bounds (S : Source) where
  lowerHeight : List Bool → ℕ
  leadingHeight : List Bool → ℕ
  lower : ∀ c, letI := S.ring c
    ∀ i e r t, (Algebra.leftMulMatrix (S.basis c) ((S.toEuler.lowerPolynomial c i).coeff e) r t).natAbs ≤ 2 ^ lowerHeight c
  leading : ∀ c, (commonLeading S c).natAbs ≤ 2 ^ leadingHeight c

def dimension (S : Source) (c : List Bool) : ℕ := FixedWidthPolynomial.count (S.free c) (S.targetWidth c)

theorem dimension_binary (S : Source) (a : Access S) : BinaryFn (dimension S) :=
  BinaryFn.of_bits (mem_FP_of_eq (FixedWidthPolynomial.countCode_mem_FP a.free a.targetWidth)
    (fun c => FixedWidthPolynomial.countCode_code _ _ c))

noncomputable def reductionMatrix (S : Source) (c : List Bool) :
    letI := S.ring c
    Matrix (Fin (dimension S c)) (Fin (dimension S c)) (S.carrier c) :=
  (IntegralPurePowerActionBits.reductionSource (relativeSource S)).matrix c

theorem reduction_height (S : Source) (B : Bounds S) (c : List Bool)
    (i j : Fin (dimension S c)) (r t : Fin (S.rank c)) :
    letI := S.ring c
    (Algebra.leftMulMatrix (S.basis c) (reductionMatrix S c i j) r t).natAbs ≤
      2 ^ (B.lowerHeight c + B.leadingHeight c) := by
  let := S.ring c
  have HL (i e) : (Algebra.leftMulMatrix (S.basis c) ((S.toEuler.lowerPolynomial c i).coeff e) r t).natAbs ≤
      2 ^ (B.lowerHeight c + B.leadingHeight c) :=
    (B.lower c i e r t).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  have HC := (IntegralReductionHeightBounds.integer_entry_height (S.basis c) (commonLeading S c)
    (B.leadingHeight c) (B.leading c) r t).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_left (B.leadingHeight c) (B.lowerHeight c)))
  exact IntegralReductionHeightBounds.matrix_height
    (IntegralPurePowerReductionBits.coefficientHom (S.basis c) r t) (S.coordinate c)
    (fun i => rowDegree S.toEuler c i.val) (S.toEuler.lowerPolynomial c) (commonLeading S c : S.carrier c)
    (S.bound c) (B.lowerHeight c + B.leadingHeight c) HL HC i j

def budget (S : Source) (B : Bounds S) (c : List Bool) : ℕ :=
  IntegralActionHeightBounds.criticalHeight (dimension S c) (S.rank c) (S.bound c)
    (B.lowerHeight c + B.leadingHeight c) (B.leadingHeight c)

theorem budget_binary (S : Source) (B : Bounds S) (a : Access S)
    (hH : BinaryFn B.lowerHeight) (hG : BinaryFn B.leadingHeight) : BinaryFn (budget S B) :=
  IntegralActionHeightBounds.criticalHeight_binary (dimension_binary S a) a.rank a.bound (hH.add hG) hG

theorem coefficient_height (S : Source) (B : Bounds S) (c : List Bool) (k : ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    (Algebra.leftMulMatrix (S.basis c) ((S.annihilator c).coeff k) r t).natAbs ≤ 2 ^ budget S B c := by
  let := S.ring c
  have : Nontrivial (S.carrier c) := (relativeSource S).nontrivial c
  let RS := IntegralPurePowerActionBits.reductionSource (relativeSource S)
  have HP : S.annihilator c = ScaledGradedReductionAnnihilator.polynomial
      (GradedReductionAnnihilator.paddedMatrix (reductionMatrix S c) (RS.normal c) (S.bound c) (RS.shift c))
      (commonLeading S c : S.carrier c) (S.bound c + 1) := by rfl
  rw [HP]
  exact IntegralActionHeightBounds.padded_annihilator_height (S.basis c) (reductionMatrix S c)
    (RS.normal c) (S.bound c) (RS.shift c) (commonLeading S c)
    (B.lowerHeight c + B.leadingHeight c) (B.leadingHeight c) (reduction_height S B c) (B.leading c) k r t

theorem budget_linear_bound (S : Source) (B : Bounds S) (c : List Bool) :
    budget S B c ≤ IntegralActionHeightBounds.criticalFactor (dimension S c) (S.rank c) (S.bound c) *
      (B.lowerHeight c + 2 * B.leadingHeight c + 1) := by
  have H := IntegralActionHeightBounds.criticalHeight_linear_bound (dimension S c) (S.rank c) (S.bound c)
    (B.lowerHeight c + B.leadingHeight c) (B.leadingHeight c)
  convert H using 1
  congr 1
  ring

end LeanCanny.Algebra.IntegralClearedCriticalBounds
