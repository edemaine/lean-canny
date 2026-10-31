/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralClearedCriticalBounds
public import LeanCanny.Algebra.IntegralFrozenConstantBounds
public import LeanCanny.Algebra.IntegralDerivativeHeightBounds

/-! # Actual critical height budgets from four original input bounds

Original spatial coefficient matrices, retained-height matrices, and the
two integer scalars supply all bounds. Differentiation precedes clearing;
the same original allowance is retained. Euler products and sums, the
common leading coefficient, and every actual relative coefficient then
have derived native binary budgets.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralOriginalCriticalBounds
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralClearedCriticalBits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

structure Inputs (S : Source) where
  coefficientHeight : List Bool → ℕ
  retainedHeight : List Bool → ℕ
  denominatorHeight : List Bool → ℕ
  leadingHeight : List Bool → ℕ
  coefficient : ∀ c, letI := S.ring c
    ∀ e r t, (Algebra.leftMulMatrix (S.basis c) ((S.polynomial c).coeff e) r t).natAbs ≤ 2 ^ coefficientHeight c
  retained : ∀ c, letI := S.ring c
    ∀ i : Fin (S.arity c), ∀ r t, (Algebra.leftMulMatrix (S.basis c) (S.height c i.val) r t).natAbs ≤ 2 ^ retainedHeight c
  denominator : ∀ c, (S.denominator c).natAbs ≤ 2 ^ denominatorHeight c
  leading : ∀ c, (S.leading c).natAbs ≤ 2 ^ leadingHeight c

def gradientBudget (S : Source) (I : Inputs S) (c : List Bool) : ℕ :=
  IntegralFrozenCoefficientBounds.coefficientHeight (S.arity c) (S.rank c) (S.sourceWidth c) (S.allowance c)
    (I.coefficientHeight c + S.sourceWidth c) (I.retainedHeight c) (I.denominatorHeight c)

def sourceBudget (S : Source) (I : Inputs S) (c : List Bool) : ℕ :=
  IntegralFrozenConstantBounds.lowerHeight (S.arity c) (S.rank c) (S.sourceWidth c) (S.allowance c)
    (I.coefficientHeight c) (I.retainedHeight c) (I.denominatorHeight c) (I.leadingHeight c)

def lowerBudget (S : Source) (I : Inputs S) (c : List Bool) : ℕ :=
  sourceBudget S I c + (S.allowance c).size + gradientBudget S I c + (S.free c).size + 1

def leadingBudget (S : Source) (I : Inputs S) (c : List Bool) : ℕ :=
  I.leadingHeight c + S.allowance c * I.denominatorHeight c + (S.allowance c).size

theorem gradientBudget_binary (S : Source) (I : Inputs S) (a : Access S)
    (hC : BinaryFn I.coefficientHeight) (hV : BinaryFn I.retainedHeight) (hQ : BinaryFn I.denominatorHeight) :
    BinaryFn (gradientBudget S I) :=
  IntegralFrozenCoefficientBounds.coefficientHeight_binary (BinaryFn.ofUnary a.arity) a.rank a.sourceWidth a.allowance
    (hC.add (BinaryFn.ofUnary a.sourceWidth)) hV hQ

theorem sourceBudget_binary (S : Source) (I : Inputs S) (a : Access S)
    (hC : BinaryFn I.coefficientHeight) (hV : BinaryFn I.retainedHeight)
    (hQ : BinaryFn I.denominatorHeight) (hP : BinaryFn I.leadingHeight) : BinaryFn (sourceBudget S I) :=
  IntegralFrozenConstantBounds.lowerHeight_binary (BinaryFn.ofUnary a.arity) a.rank a.sourceWidth a.allowance hC hV hQ hP

theorem lowerBudget_binary (S : Source) (I : Inputs S) (a : Access S)
    (hC : BinaryFn I.coefficientHeight) (hV : BinaryFn I.retainedHeight)
    (hQ : BinaryFn I.denominatorHeight) (hP : BinaryFn I.leadingHeight) : BinaryFn (lowerBudget S I) :=
  ((((sourceBudget_binary S I a hC hV hQ hP).add a.allowance.size).add
    (gradientBudget_binary S I a hC hV hQ)).add (BinaryFn.ofUnary a.free).size).add (BinaryFn.const 1)

theorem leadingBudget_binary (S : Source) (I : Inputs S) (a : Access S)
    (hQ : BinaryFn I.denominatorHeight) (hP : BinaryFn I.leadingHeight) : BinaryFn (leadingBudget S I) :=
  (hP.add (a.allowance.mul hQ)).add a.allowance.size

theorem gradient_height (S : Source) (I : Inputs S) (c : List Bool) (j : Fin (S.free c))
    (m : Fin (S.free c) →₀ ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    (Algebra.leftMulMatrix (S.basis c) ((IntegralCriticalGradientBits.polynomial S.toEuler.toGradient c j).coeff m) r t).natAbs ≤
      2 ^ gradientBudget S I c := by
  let := S.ring c
  exact IntegralFrozenCoefficientBounds.coefficient_height (S.basis c) (S.denominator c) (S.height c)
    (S.offset c) (S.free c) (S.allowance c) (S.sourceWidth c) (I.coefficientHeight c + S.sourceWidth c)
    (I.retainedHeight c) (I.denominatorHeight c)
    (MvPolynomial.pderiv (IntegralCriticalGradientBits.freeIndex S.toEuler.toGradient c j) (S.polynomial c))
    (IntegralDerivativeHeightBounds.support_bounds _ _ (S.support c) _)
    (IntegralDerivativeHeightBounds.matrix_coefficient_height (S.basis c) _ _ _ (S.support c) (I.coefficient c) _)
    (I.retained c) (I.denominator c) m r t

theorem source_height (S : Source) (I : Inputs S) (c : List Bool)
    (m : Fin (S.free c) →₀ ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    (Algebra.leftMulMatrix (S.basis c) ((S.toEuler.toGradient.toFrozen.lowerPolynomial c).coeff m) r t).natAbs ≤
      2 ^ sourceBudget S I c := by
  let := S.ring c
  exact IntegralFrozenConstantBounds.lower_height (S.basis c) (S.denominator c) (S.leading c) (S.height c)
    (S.offset c) (S.free c) (S.allowance c) (S.sourceWidth c) (I.coefficientHeight c)
    (I.retainedHeight c) (I.denominatorHeight c) (I.leadingHeight c) (S.polynomial c)
    (S.support c) (I.coefficient c) (I.retained c) (I.denominator c) (I.leading c) m r t

theorem spatial_product_height (S : Source) (I : Inputs S) (c : List Bool) (j : Fin (S.free c))
    (m : Fin (S.free c) →₀ ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    (Algebra.leftMulMatrix (S.basis c)
      ((MvPolynomial.X j * IntegralCriticalGradientBits.polynomial S.toEuler.toGradient c j).coeff m) r t).natAbs ≤
        2 ^ gradientBudget S I c := by
  let := S.ring c
  rw [MvPolynomial.coeff_X_mul']
  split_ifs
  · exact gradient_height S I c j _ r t
  · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
    exact Nat.zero_le _

attribute [local irreducible] IntegralCriticalGradientBits.polynomial

theorem sum_height (S : Source) (I : Inputs S) (c : List Bool) (m : Fin (S.free c) →₀ ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    (Algebra.leftMulMatrix (S.basis c) ((S.toEuler.sumPolynomial c).coeff m) r t).natAbs ≤
      2 ^ (gradientBudget S I c + (S.free c).size) := by
  let := S.ring c
  let f : Fin (S.free c) → ℤ := fun j => Algebra.leftMulMatrix (S.basis c)
    ((if j = S.objective c then 0 else MvPolynomial.X j * IntegralCriticalGradientBits.polynomial S.toEuler.toGradient c j).coeff m) r t
  have HF (j : Fin (S.free c)) : (f j).natAbs ≤ 2 ^ gradientBudget S I c := by
    dsimp only [f]
    by_cases hj : j = S.objective c
    · simp only [ite_eq_left hj, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero, Matrix.zero_apply, Int.natAbs_zero]
      exact Nat.zero_le _
    · rw [ite_eq_right hj]
      exact spatial_product_height S I c j m r t
  have HS : Algebra.leftMulMatrix (S.basis c) ((S.toEuler.sumPolynomial c).coeff m) r t = ∑ j, f j := by
    rw [IntegralEulerBits.Source.sumPolynomial, MvPolynomial.coeff_sum, map_sum, Matrix.sum_apply]
  rw [HS]
  calc
    _ ≤ ∑ j : Fin (S.free c), (f j).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _j : Fin (S.free c), 2 ^ gradientBudget S I c := by
      apply Finset.sum_le_sum
      intro j _
      exact HF j
    _ = S.free c * 2 ^ gradientBudget S I c := by simp
    _ ≤ 2 ^ (S.free c).size * 2 ^ gradientBudget S I c := Nat.mul_le_mul_right _ (Nat.lt_size_self (S.free c)).le
    _ = _ := by rw [← pow_add, Nat.add_comm]

theorem objective_height (S : Source) (I : Inputs S) (c : List Bool) (m : Fin (S.free c) →₀ ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    (Algebra.leftMulMatrix (S.basis c) ((S.toEuler.objectivePolynomial c).coeff m) r t).natAbs ≤ 2 ^ lowerBudget S I c := by
  let := S.ring c
  unfold IntegralEulerBits.Source.objectivePolynomial
  rw [IntegralEulerBits.objective_coefficient]
  have HD : ((S.allowance c : ℤ) * Algebra.leftMulMatrix (S.basis c)
      ((S.toEuler.toGradient.toFrozen.lowerPolynomial c).coeff m) r t).natAbs ≤
        2 ^ (sourceBudget S I c + (S.allowance c).size) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact (Nat.mul_le_mul (Nat.lt_size_self (S.allowance c)).le (source_height S I c m r t)).trans_eq (by
      rw [← pow_add, Nat.add_comm])
  have H := IntegralFrozenConstantBounds.subtract_bound _ _ _ _ HD (sum_height S I c m r t)
  convert H using 1
  congr 1
  unfold lowerBudget
  omega

theorem lower_height (S : Source) (I : Inputs S) (c : List Bool) (j : Fin (S.free c))
    (m : Fin (S.free c) →₀ ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    (Algebra.leftMulMatrix (S.basis c) ((S.toEuler.lowerPolynomial c j).coeff m) r t).natAbs ≤ 2 ^ lowerBudget S I c := by
  let := S.ring c
  unfold IntegralEulerBits.Source.lowerPolynomial
  by_cases hj : j = S.objective c
  · rw [ite_eq_left hj]
    exact objective_height S I c m r t
  · rw [ite_eq_right hj]
    exact (gradient_height S I c j m r t).trans (Nat.pow_le_pow_right (by decide) (by unfold lowerBudget; omega))

theorem leading_height (S : Source) (I : Inputs S) (c : List Bool) :
    (IntegralClearedCriticalBounds.commonLeading S c).natAbs ≤ 2 ^ leadingBudget S I c := by
  unfold IntegralClearedCriticalBounds.commonLeading
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  calc
    _ ≤ 2 ^ I.leadingHeight c * (2 ^ I.denominatorHeight c) ^ S.allowance c * 2 ^ (S.allowance c).size :=
      Nat.mul_le_mul (Nat.mul_le_mul (I.leading c) (Nat.pow_le_pow_left (I.denominator c) _)) (Nat.lt_size_self _).le
    _ = _ := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      unfold leadingBudget
      congr 1
      ring

def derived (S : Source) (I : Inputs S) : IntegralClearedCriticalBounds.Bounds S where
  lowerHeight := lowerBudget S I
  leadingHeight := leadingBudget S I
  lower := lower_height S I
  leading := leading_height S I

def budget (S : Source) (I : Inputs S) : List Bool → ℕ := IntegralClearedCriticalBounds.budget S (derived S I)

theorem budget_binary (S : Source) (I : Inputs S) (a : Access S)
    (hC : BinaryFn I.coefficientHeight) (hV : BinaryFn I.retainedHeight)
    (hQ : BinaryFn I.denominatorHeight) (hP : BinaryFn I.leadingHeight) : BinaryFn (budget S I) :=
  IntegralClearedCriticalBounds.budget_binary S (derived S I) a
    (lowerBudget_binary S I a hC hV hQ hP) (leadingBudget_binary S I a hQ hP)

theorem coefficient_height (S : Source) (I : Inputs S) (c : List Bool) (k : ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    (Algebra.leftMulMatrix (S.basis c) ((S.annihilator c).coeff k) r t).natAbs ≤ 2 ^ budget S I c :=
  IntegralClearedCriticalBounds.coefficient_height S (derived S I) c k r t

end LeanCanny.Algebra.IntegralOriginalCriticalBounds
