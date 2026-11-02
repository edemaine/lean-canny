/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CharacteristicIntegerBounds
public import LeanCanny.Algebra.ScaledGradedReductionAnnihilator
/-! # Integer height metadata after a scalar characteristic substitution -/
@[expose] public section
namespace LeanCanny.Algebra.ScaledCharacteristicIntegerBounds
open LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def coefficientHeight (n H S : ℕ) := CharacteristicIntegerBounds.budget n H+S*n
def massHeight (n H S : ℕ) := n.size+coefficientHeight n H S

theorem coefficientHeight_binary {n H S : List Bool → ℕ} (hn : BinaryFn n) (hH : BinaryFn H) (hS : BinaryFn S) :
    BinaryFn (fun q=>coefficientHeight (n q) (H q) (S q)) := (CharacteristicIntegerBounds.budget_binary hn hH).add (hS.mul hn)
theorem massHeight_binary {n H S : List Bool → ℕ} (hn : BinaryFn n) (hH : BinaryFn H) (hS : BinaryFn S) :
    BinaryFn (fun q=>massHeight (n q) (H q) (S q)) := hn.size.add (coefficientHeight_binary hn hH hS)

theorem degree {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) (hc : c≠0) :
    (ScaledGradedReductionAnnihilator.polynomial M c 1).natDegree=n := by
  rw [ScaledGradedReductionAnnihilator.polynomial,pow_one,Polynomial.natDegree_comp,
    Matrix.charpoly_natDegree_eq_dim,Polynomial.natDegree_C_mul_X _ hc,Nat.mul_one,Fintype.card_fin]

theorem leading {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) (hc : c≠0) :
    (ScaledGradedReductionAnnihilator.polynomial M c 1).leadingCoeff=c^n := by
  have HD : (Polynomial.C c*Polynomial.X).natDegree≠0 := by rw [Polynomial.natDegree_C_mul_X _ hc]; decide
  rw [ScaledGradedReductionAnnihilator.polynomial,pow_one,Polynomial.leadingCoeff_comp HD,
    (Matrix.charpoly_monic M).leadingCoeff,one_mul,Polynomial.leadingCoeff_C_mul_X,
    Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin]

theorem nonzero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) (hc : c≠0) :
    ScaledGradedReductionAnnihilator.polynomial M c 1≠0 := by
  intro h
  have HH := congrArg Polynomial.leadingCoeff h
  rw [leading M c hc,Polynomial.leadingCoeff_zero] at HH
  exact pow_ne_zero _ hc HH

theorem coefficient_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) (H S : ℕ)
    (hM : ∀ r t,(M r t).natAbs≤2^H) (hc : c.natAbs≤2^S) (k : ℕ) :
    ((ScaledGradedReductionAnnihilator.polynomial M c 1).coeff k).natAbs≤2^coefficientHeight n H S := by
  rw [ScaledGradedReductionAnnihilator.coefficient,Nat.one_mul]
  by_cases hk : k≤n
  · have HC := (Nat.lt_size_self (M.charpoly.coeff k).natAbs).le.trans
      (Nat.pow_le_pow_right (by decide) (CharacteristicIntegerBounds.coefficient_bits M H hM k))
    rw [Int.natAbs_mul,Int.natAbs_pow]
    calc
      _ ≤ 2^CharacteristicIntegerBounds.budget n H*(2^S)^k := Nat.mul_le_mul HC (Nat.pow_le_pow_left hc k)
      _ = 2^(CharacteristicIntegerBounds.budget n H+S*k) := by rw [←pow_mul,←pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (Nat.mul_le_mul_left S hk) _)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin]; omega),zero_mul,Int.natAbs_zero]
    exact Nat.zero_le _

theorem mass_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) (H S : ℕ) (hc0 : c≠0)
    (hM : ∀ r t,(M r t).natAbs≤2^H) (hc : c.natAbs≤2^S) :
    coefficientMass (ScaledGradedReductionAnnihilator.polynomial M c 1)≤2^massHeight n H S := by
  have HH := coefficientMass_le (ScaledGradedReductionAnnihilator.polynomial M c 1) n (2^coefficientHeight n H S)
    (degree M c hc0).le (coefficient_bound M c H S hM hc)
  have HR : n+1≤2^n.size := by have HN := Nat.lt_size_self n; omega
  apply HH.trans
  simpa only [massHeight,pow_add] using Nat.mul_le_mul_right (2^coefficientHeight n H S) HR

end LeanCanny.Algebra.ScaledCharacteristicIntegerBounds
