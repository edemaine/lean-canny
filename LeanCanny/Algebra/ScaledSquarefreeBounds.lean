/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ScaledSquarefreeSpace

/-! # Source-derived coefficient heights for square-free preprocessing

The Cramer dimension is at most the original degree plus one. Combining the
derivative-GCD determinant bound with the original coefficient height gives
an FP output-height writer, independent of the computed GCD degree.
-/

@[expose] public section

namespace LeanCanny.Algebra.SeparableBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
attribute [local irreducible] BinaryNat.add

noncomputable def gcdBudget (F : Family) : List Bool → ℕ := (resultantFamily F).integer.budget

noncomputable def squarefreeBudget (F : Family) (c : List Bool) : ℕ :=
  ((F.polynomial c).natDegree + 1).size * ((F.polynomial c).natDegree + 1) +
    ((F.polynomial c).natDegree + 1) * (gcdBudget F c + F.height c) + 1

theorem gcd_coefficient_bound (F : Family) (c : List Bool) (k : ℕ) :
    ((ScaledSquarefree.gcd (F.polynomial c)).coeff k).natAbs ≤ 2 ^ gcdBudget F c := by
  have hp (i : ℕ) : ((F.polynomial c).coeff i).natAbs ≤ 2 ^ (F.height c + (F.polynomial c).natDegree.size) :=
    (F.coefficient_bound c i).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hs : ((ScaledSquarefree.gcd (F.polynomial c)).coeff k).natAbs.size ≤ gcdBudget F c := by
    have h := PolynomialGCDBits.representative_coeff_size (F.polynomial c) (F.polynomial c).derivative
      (F.height c + (F.polynomial c).natDegree.size) (F.height c + (F.polynomial c).natDegree.size) k
      hp (derivative_bound _ _ (F.coefficient_bound c))
    simpa only [ScaledSquarefree.gcd, gcdBudget, Resultant.Family.integer, resultantFamily,
      natDegree_derivative, Nat.add_mul, Nat.add_assoc] using h
  exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hs)

theorem squarefree_coefficient_size (F : Family) (c : List Bool) (k : ℕ) :
    ((ScaledSquarefree.polynomial (F.polynomial c)).coeff k).natAbs.size ≤ squarefreeBudget F c := by
  have hp (i : ℕ) : ((ScaledSquarefree.gcd (F.polynomial c)).coeff i).natAbs ≤ 2 ^ (gcdBudget F c + F.height c) :=
    (gcd_coefficient_bound F c i).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hq (i : ℕ) : ((F.polynomial c).coeff i).natAbs ≤ 2 ^ (gcdBudget F c + F.height c) :=
    (F.coefficient_bound c i).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have h := ScaledPolynomialQuotient.quotient_coeff_size (ScaledSquarefree.gcd (F.polynomial c)) (F.polynomial c)
    (ScaledSquarefree.degree (F.polynomial c)) ((F.polynomial c).natDegree - ScaledSquarefree.degree (F.polynomial c))
    (gcdBudget F c + F.height c) k hp hq
  have hN : (F.polynomial c).natDegree - ScaledSquarefree.degree (F.polynomial c) + 1 ≤
      (F.polynomial c).natDegree + 1 := by omega
  exact h.trans (Nat.add_le_add_right (Nat.add_le_add
    (Nat.mul_le_mul (Nat.size_le_size hN) hN) (Nat.mul_le_mul_right _ hN)) 1)

noncomputable def budgetAccess (F : Family) (A : Readers F) : SylvesterBits.Access where
  leftDegree := BinaryNat.succ ∘ A.degree
  rightDegree _ := []
  coefficientBits c := BinaryNat.add (pair (SylvesterBits.budget (access F A).bits c) (A.height c))
  leftCoefficient _ := []
  rightCoefficient _ := []

theorem budgetAccess_controls (F : Family) (A : Readers F) : (budgetAccess F A).ControlsPolyTime := by
  have hl := mem_FP_comp A.degreeFP BinaryNat.succ_mem_FP
  have hg := SylvesterBits.budget_mem_FP_of_controls (access F A).bits (access_controls F A)
  have hb := mem_FP_comp (mem_FP_pair hg A.heightFP) BinaryNat.add_mem_FP
  have hb' : (fun c => BinaryNat.add (pair (SylvesterBits.budget (access F A).bits c) (A.height c))) ∈ FP :=
    mem_FP_of_eq hb (fun _ => rfl)
  exact ⟨hl, constFn_mem_FP [], hb'⟩

noncomputable def squarefreeBudgetCode (F : Family) (A : Readers F) : List Bool → List Bool := SylvesterBits.budget (budgetAccess F A)

theorem squarefreeBudgetCode_FP (F : Family) (A : Readers F) : squarefreeBudgetCode F A ∈ FP :=
  SylvesterBits.budget_mem_FP_of_controls (budgetAccess F A) (budgetAccess_controls F A)

theorem squarefreeBudgetCode_eq (F : Family) (A : Readers F) (c : List Bool) :
    squarefreeBudgetCode F A c = BinaryNatCode.encode (squarefreeBudget F c) := by
  have hg := (access F A).integer.budget_eq c
  change SylvesterBits.budget (access F A).bits c = BinaryNatCode.encode (gcdBudget F c) at hg
  have hl : (budgetAccess F A).leftDegree c = BinaryNatCode.encode ((F.polynomial c).natDegree + 1) := by
    simp only [budgetAccess, Function.comp_apply, A.degree_eq, BinaryNat.succ_eq_bits,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hb : (budgetAccess F A).coefficientBits c = BinaryNatCode.encode (gcdBudget F c + F.height c) := by
    simp only [budgetAccess, hg, A.height_eq, BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have h := SylvesterBits.budget_code (budgetAccess F A) c _ 0 _ hl rfl hb
  simpa only [squarefreeBudgetCode, squarefreeBudget, Nat.add_zero] using h

theorem squarefree_coefficient_bound (F : Family) (A : Readers F) (c : List Bool) (k : ℕ) :
    ((ScaledSquarefree.polynomial (F.polynomial c)).coeff k).natAbs ≤
      2 ^ Nat.fromBitsLE (squarefreeBudgetCode F A c) := by
  rw [squarefreeBudgetCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) (squarefree_coefficient_size F c k))

theorem scaledSquarefreeDegreeEvaluator (F : Family) (A : Readers F) (hne : ∀ c, F.polynomial c ≠ 0) :
    SpaceFunction (fun c => BinaryNatCode.encode (ScaledSquarefree.polynomial (F.polynomial c)).natDegree) :=
  (squarefreeDegreeEvaluator F A hne).congr (funext fun c => congrArg BinaryNatCode.encode
    (ScaledSquarefree.polynomial_natDegree _ (hne c)).symm)

end LeanCanny.Algebra.SeparableBits
