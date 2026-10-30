/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerPolynomialDegreeSpace
public import LeanCanny.Algebra.DyadicConstantCoefficient
public import LeanCanny.Computation.SpaceFunctionSpaceBranch
public import LeanCanny.Computation.PSPACEClosure

/-! # Replacing zero polynomial factors by one in native space

Polynomial-zero detection scans the original modular coefficient reader with
binary degree and mass budgets. Its workspace is charged when selecting a
factor. Neither the actual degree nor the zero flag is FP metadata.
-/

@[expose] public section
namespace LeanCanny.Algebra.ZeroAwarePolynomialBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Encoding.Brackets
open scoped Classical

noncomputable def polynomial (p : List Bool → ℤ[X]) (c : List Bool) : ℤ[X] := if p c = 0 then 1 else p c

theorem zeroDecider (p : List Bool → ℤ[X]) (P : SpaceFunction (PrimitivePairBits.coefficient p))
    (D b : List Bool → ℕ) (hD : BinaryFn D) (hb : BinaryFn b)
    (hd : ∀ c, (p c).natDegree ≤ D c) (hm : ∀ c, coefficientMass (p c) ≤ 2 ^ b c) :
    SpaceDecider {c | p c = 0} := by
  have E := PolynomialDegreeBits.offsetEvaluator (IntegerPolynomialBits.signEvaluator p P b hb hm)
    (fun c => BinaryNatCode.encode (D c)) hD.bits_mem_FP p
    (fun c => by simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using hd c) (by
      intro c i
      simp only [IntegerPolynomialBits.value, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      by_cases hz : (p c).coeff i = 0
      · simp [hz]
      · simp only [hz, ite_false]
        split_ifs <;> simp)
  apply E.decider (fun w => decide (w = [])) (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  intro c
  by_cases hz : p c = 0 <;> simp [hz, BinaryNatCode.encode, BinaryNat.bits_eq_nil_iff]

theorem coefficientEvaluator (p : List Bool → ℤ[X]) (P : SpaceFunction (PrimitivePairBits.coefficient p))
    (D b : List Bool → ℕ) (hD : BinaryFn D) (hb : BinaryFn b)
    (hd : ∀ c, (p c).natDegree ≤ D c) (hm : ∀ c, coefficientMass (p c) ≤ 2 ^ b c) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial p)) := by
  have Z := (zeroDecider p P D b hD hb hd hm).precompose
    RationalSubstitution.IntegerBits.context RationalSubstitution.IntegerBits.context_mem_FP
  have E := SpaceFunction.branchDecider Z DyadicConstantBits.oneCoefficientEvaluator P
  refine E.congr (funext fun q => ?_)
  by_cases hz : p (RationalSubstitution.IntegerBits.context q) = 0
  all_goals simp only [Set.mem_preimage, Set.mem_ofPred_eq, PrimitivePairBits.coefficient,
    polynomial, hz, ite_true, ite_false]

theorem ne_zero (p : List Bool → ℤ[X]) (c : List Bool) : polynomial p c ≠ 0 := by
  unfold polynomial
  split_ifs with h
  · exact one_ne_zero
  · exact h

theorem degree_le (p : List Bool → ℤ[X]) (D : List Bool → ℕ) (hd : ∀ c, (p c).natDegree ≤ D c) (c : List Bool) :
    (polynomial p c).natDegree ≤ D c := by
  unfold polynomial
  split_ifs
  · simp
  · exact hd c

theorem mass_le (p : List Bool → ℤ[X]) (b : List Bool → ℕ) (hm : ∀ c, coefficientMass (p c) ≤ 2 ^ b c) (c : List Bool) :
    coefficientMass (polynomial p c) ≤ 2 ^ b c := by
  unfold polynomial
  split_ifs
  · change coefficientMass (C (1 : ℤ)) ≤ _
    rw [coefficientMass_C]
    exact Nat.one_le_pow _ _ (by decide)
  · exact hm c

end LeanCanny.Algebra.ZeroAwarePolynomialBits
