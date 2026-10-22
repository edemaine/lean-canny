/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ScaledSquarefreePadding
public import LeanCanny.Algebra.BalancedTableCoefficientSpace
public import LeanCanny.Algebra.BalancedCanonicalDegrees

/-! # Original readers with canonical indexed inputs and X padding

Only indices below the finite source count use the original polynomial.
All others use X. The original coefficient reader and FP controls give native
readers on every word. Nonzeroness is needed only for the actual finite family.
Square-free leaves then agree literally with the finite-annihilator leaves.
-/

@[expose] public section

namespace LeanCanny.Algebra.PaddedAnnihilatorBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open LeanCanny.Encoding.Brackets
open SeparableBits (Family Readers)
open scoped Classical

def input (p : List Bool) : List Bool := pair (pairFst p) (BinaryNat.normalize (pairSnd p))
def valid (count : List Bool → ℕ) (p : List Bool) : Prop := Nat.fromBitsLE (pairSnd p) < count (pairFst p)

attribute [local irreducible] BinaryNat.normalize BinaryNat.succ

theorem input_FP : input ∈ FP := mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)

theorem input_packet (c : List Bool) (i : ℕ) : input (pair c (BinaryNatCode.encode i)) = pair c (BinaryNatCode.encode i) := by
  simp only [input, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem valid_FP {count : List Bool → ℕ} (hn : UnaryFn count) : FPPred (valid count) := by
  have h := BinaryNat.lt_fppred pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP (bits_mem_FP hn))
  exact h.of_iff (fun p => by simp only [Function.comp_apply, Nat.fromBitsLE_bits, valid])

noncomputable def family (B : Family) (count : List Bool → ℕ) : Family where
  polynomial p := if valid count p then B.polynomial (input p) else X
  height p := B.height (input p)
  coefficient_bound p k := by
    split_ifs
    · exact B.coefficient_bound _ _
    · have h : ((X : ℤ[X]).coeff k).natAbs ≤ 1 := by simp only [coeff_X]; split_ifs <;> norm_num
      exact h.trans Nat.one_le_two_pow

theorem polynomial_packet (B : Family) (count : List Bool → ℕ) (c : List Bool) (i : ℕ) :
    (family B count).polynomial (pair c (BinaryNatCode.encode i)) =
      if i < count c then B.polynomial (pair c (BinaryNatCode.encode i)) else X := by
  change (if valid count (pair c (BinaryNatCode.encode i)) then
    B.polynomial (input (pair c (BinaryNatCode.encode i))) else X) = _
  rw [input_packet]
  simp only [valid, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

def paddingCoefficient (p : List Bool) : List Bool :=
  if BinaryNat.normalize (pairSnd p) = [true] then
    ArithmeticBits.one (BinaryNat.succ (pairSnd (pairFst p))) else []

theorem paddingCoefficient_FP : paddingCoefficient ∈ FP := by
  have hp := stringEq_fppred (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP) (constFn_mem_FP [true])
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.succ_mem_FP
  have ho := mem_FP_comp hm ArithmeticBits.one_mem_FP
  have h := hp.ite_mem_FP ho (constFn_mem_FP [])
  exact mem_FP_of_eq h (fun p => by simp only [paddingCoefficient, Function.comp_apply])

theorem paddingCoefficient_packet (q : List Bool) (k : ℕ) :
    paddingCoefficient (pair q (BinaryNatCode.encode k)) =
      residueBits ((((X : ℤ[X]).coeff k) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  have he : BinaryNat.normalize (BinaryNatCode.encode k) = [true] ↔ k = 1 := by
    rw [BinaryNat.normalize_eq_bits]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    change BinaryNatCode.encode k = BinaryNatCode.encode 1 ↔ k = 1
    exact BinaryNatCode.encode_injective.eq_iff
  simp only [paddingCoefficient, pairFst_pair, pairSnd_pair, he, BinaryNat.succ_eq_bits]
  by_cases hk : k = 1
  · subst k
    rw [ite_eq_left rfl]
    simpa only [coeff_X, ite_true, Int.cast_one, BinaryNatCode.encode] using
      ArithmeticBits.one_residueBits (Nat.fromBitsLE (pairSnd q) + 1)
  · rw [ite_eq_right hk]
    simp only [coeff_X, Ne.symm hk, ite_false, Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

noncomputable def coefficient (B : Family) (A : Readers B) (count : List Bool → ℕ) (p : List Bool) : List Bool :=
  if valid count (pairFst (pairFst p)) then A.coefficient (SeparableBits.reindexQuery input p) else paddingCoefficient p

theorem coefficientEvaluator (B : Family) (A : Readers B) (count : List Bool → ℕ) (hn : UnaryFn count) :
    SpaceFunction (coefficient B A count) := by
  have hp := (valid_FP hn).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have E := SpaceFunction.branch (fun p => decide (valid count (pairFst (pairFst p)))) hp.flag_mem_FP
    (A.evaluator.precompose (SeparableBits.reindexQuery input) (SeparableBits.reindexQuery_FP input input_FP))
    (SpaceFunction.ofFP _ paddingCoefficient_FP)
  exact E.congr (funext fun p => by simp only [coefficient, Function.comp_apply, decide_eq_true_eq])

noncomputable def readers (B : Family) (A : Readers B) (count : List Bool → ℕ) (hn : UnaryFn count) : Readers (family B count) where
  degree p := if valid count p then A.degree (input p) else BinaryNatCode.encode 1
  height := A.height ∘ input
  coefficient := coefficient B A count
  degreeFP := (valid_FP hn).ite_mem_FP (mem_FP_comp input_FP A.degreeFP) (constFn_mem_FP (BinaryNatCode.encode 1))
  heightFP := mem_FP_comp input_FP A.heightFP
  degree_eq p := by
    by_cases hp : valid count p
    · simp only [hp, ite_true, family, A.degree_eq]
    · simp only [hp, ite_false, family, natDegree_X]
  height_eq p := A.height_eq _
  coefficient_eq q k := by
    simp only [coefficient, pairFst_pair]
    by_cases hp : valid count (pairFst q)
    · rw [ite_eq_left hp]
      have h := (A.reindex input input_FP).coefficient_eq q k
      simpa only [SeparableBits.Readers.reindex, SeparableBits.Family.reindex, Function.comp_apply, family, hp, ite_true] using h
    · rw [ite_eq_right hp, paddingCoefficient_packet]
      simp only [family, hp, ite_false]
  evaluator := coefficientEvaluator B A count hn

theorem nonzero (B : Family) (count : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0) (p : List Bool) :
    (family B count).polynomial p ≠ 0 := by
  by_cases hp : valid count p
  · simp only [family, hp, ite_true, input, BinaryNat.normalize_eq_bits]
    exact hne (pairFst p) (Nat.fromBitsLE (pairSnd p)) hp
  · simp only [family, hp, ite_false]
    exact X_ne_zero

theorem squarefree_leaf (B : Family) (count : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0) (c : List Bool) (i : ℕ) :
    ScaledSquarefree.polynomial ((family B count).polynomial (pair c (BinaryNatCode.encode i))) =
      (FiniteAnnihilatorTree.leaf (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c) i).polynomial := by
  rw [polynomial_packet]
  by_cases hi : i < count c
  · rw [ite_eq_left hi, FiniteAnnihilatorTree.leaf, dite_eq_left hi]
    rfl
  · rw [ite_eq_right hi, ScaledSquarefree.polynomial_X, FiniteAnnihilatorTree.leaf, dite_eq_right hi]
    rfl

theorem tableEvaluator (B : Family) (A : Readers B) (count : List Bool → ℕ) (hn : UnaryFn count) :
    SpaceFunction (BalancedTablePolynomials.nodeValue (family B count)) :=
  BalancedTablePolynomials.evaluator (family B count) (readers B A count hn)

end LeanCanny.Algebra.PaddedAnnihilatorBits
