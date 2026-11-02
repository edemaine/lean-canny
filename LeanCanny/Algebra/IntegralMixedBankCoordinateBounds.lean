/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedBankCoordinatePolynomial
public import LeanCanny.Algebra.CommonIntegerDenominatorBounds
/-! # Original bank bounds control quotient-coordinate annihilators

The common denominator and common-cleared matrix are bounded directly from
the verified old bank. No later source, sampler width or evaluator is involved.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedBankCoordinatePolynomial
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def coefficientBudget (m B G : ℕ) :=
  CharacteristicIntegerBounds.budget (FixedWidthPolynomial.count m B) (G+m*G)+m*G*FixedWidthPolynomial.count m B

def massBudget (m B G : ℕ) := (FixedWidthPolynomial.count m B).size+coefficientBudget m B G

theorem coefficientBudget_binary {m B G : List Bool→ℕ} (hm : UnaryFn m) (hB : UnaryFn B) (hG : BinaryFn G) :
    BinaryFn (fun q => coefficientBudget (m q) (B q) (G q)) := by
  have HR := ((BinaryFn.const 2).powUnary hB).powUnary hm
  have HM := (BinaryFn.ofUnary hm).mul hG
  exact (CharacteristicIntegerBounds.budget_binary HR (hG.add HM)).add (HM.mul HR)

theorem massBudget_binary {m B G : List Bool→ℕ} (hm : UnaryFn m) (hB : UnaryFn B) (hG : BinaryFn G) :
    BinaryFn (fun q => massBudget (m q) (B q) (G q)) :=
  (((BinaryFn.const 2).powUnary hB).powUnary hm).size.add (coefficientBudget_binary hm hB hG)

variable {n S B m G : ℕ} {P : SpatialSource n} {ι : Type}

theorem common_bound (x : State P S B m ι) (HG : x.bank.Bounds G) :
    (commonDenominator x).natAbs≤2^(m*G) := by
  have H := CommonIntegerDenominator.denominator_height Finset.univ x.bank.denominator G (fun i _ => HG.denominator i)
  simpa only [commonDenominator,Finset.card_univ,Fintype.card_fin] using H

theorem matrix_bound (x : State P S B m ι) (HG : x.bank.Bounds G) (i : Fin m)
    (r t : Fin (FixedWidthPolynomial.count m B)) : (matrix x i r t).natAbs≤2^(G+m*G) := by
  have H := CommonIntegerDenominator.numerator_height x.sampler.scalarPrefix.basis.finBasis Finset.univ
    x.bank.denominator x.bank.numerator G G (fun j _ => HG.denominator j) i (HG.numerator i) r t
  simpa only [matrix,cleared,Finset.card_univ,Fintype.card_fin] using H

theorem coefficient_bound (x : State P S B m ι) (HG : x.bank.Bounds G) (i : Fin m) (k : ℕ) :
    ((polynomial x i).coeff k).natAbs≤2^coefficientBudget m B G := by
  by_cases hk : k≤FixedWidthPolynomial.count m B
  · have HC := (Nat.lt_size_self ((matrix x i).charpoly.coeff k).natAbs).le.trans
      (Nat.pow_le_pow_right (by decide) (CharacteristicIntegerBounds.coefficient_bits (matrix x i) (G+m*G) (matrix_bound x HG i) k))
    rw [coefficient,Int.natAbs_mul,Int.natAbs_pow]
    calc
      _ ≤ 2^CharacteristicIntegerBounds.budget (FixedWidthPolynomial.count m B) (G+m*G)*(2^(m*G))^k :=
        Nat.mul_le_mul HC (Nat.pow_le_pow_left (common_bound x HG) k)
      _ = 2^(CharacteristicIntegerBounds.budget (FixedWidthPolynomial.count m B) (G+m*G)+m*G*k) := by rw [←pow_mul,←pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (Nat.mul_le_mul_left (m*G) hk) _)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [degree]; omega),Int.natAbs_zero]
    exact Nat.zero_le _

theorem mass_bound (x : State P S B m ι) (HG : x.bank.Bounds G) (i : Fin m) :
    coefficientMass (polynomial x i)≤2^massBudget m B G := by
  have HC := coefficientMass_le (polynomial x i) (FixedWidthPolynomial.count m B) (2^coefficientBudget m B G)
    (degree x i).le (coefficient_bound x HG i)
  have HR : FixedWidthPolynomial.count m B+1≤2^(FixedWidthPolynomial.count m B).size := by
    have H := Nat.lt_size_self (FixedWidthPolynomial.count m B)
    omega
  apply HC.trans
  rw [massBudget,pow_add]
  exact Nat.mul_le_mul_right _ HR

end LeanCanny.Algebra.IntegralMixedBankCoordinatePolynomial
