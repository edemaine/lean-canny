/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UnivariateRationalSubstitutionMatrix
public import LeanCanny.Algebra.MatrixPowerArithmeticFP

/-! # Native entries of a fixed-exponent substitution matrix

Clearing the monomial X^r gives n^r*d^(e-r), or zero when r exceeds e.
Thus the existing rational-substitution evaluator supplies each matrix entry
from the two space-bounded coordinate coefficient readers.
-/

@[expose] public section

namespace LeanCanny.Algebra.UnivariateRational
open Polynomial

theorem clear_X_pow (e r : ℕ) (n d : ℤ[X]) :
    clear e (X ^ r) n d = if r ≤ e then n ^ r * d ^ (e - r) else 0 := by
  classical
  unfold clear
  by_cases hr : r ≤ e
  · rw [ite_eq_left hr, Finset.sum_eq_single r]
    · simp only [Polynomial.coeff_X_pow, ite_true, Polynomial.C_1, one_mul]
    · intro k _ hkr
      simp only [Polynomial.coeff_X_pow, hkr, ite_false, Polynomial.C_0, zero_mul]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [ite_eq_right hr]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hne : r ≠ k := by omega
    simp only [Polynomial.coeff_X_pow, Ne.symm hne, ite_false, Polynomial.C_0, zero_mul]

end LeanCanny.Algebra.UnivariateRational

namespace LeanCanny.Algebra.ClearingMatrixBits
open Polynomial UnivariateRational
open LeanCanny.Encoding LeanCanny.Computation
open MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree mValue coefficientResidue)

def monomialValue (r : List Bool → ℕ) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (selectedDegree q) = r (context q) then ArithmeticBits.one (BinaryNat.succ (pairSnd q)) else []

attribute [local irreducible] BinaryNat.succ

theorem monomialValue_FP (r : List Bool → ℕ) (hr : BinaryFn r) : monomialValue r ∈ FP := by
  have hr' := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP hr.bits_mem_FP
  have hp : FPPred (fun q => Nat.fromBitsLE (selectedDegree q) = r (context q)) :=
    by simpa only [Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
      BinaryNat.eq_fppred RationalSubstitution.IntegerBits.selectedDegree_mem_FP hr'
  have ho := mem_FP_comp (mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP) ArithmeticBits.one_mem_FP
  have h := hp.ite_mem_FP ho (constFn_mem_FP [])
  exact mem_FP_of_eq h (fun _ => rfl)

theorem monomialEvaluator (r : List Bool → ℕ) (hr : BinaryFn r) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => (X : ℤ[X]) ^ r c)) := by
  have E := SpaceFunction.ofFP _ (monomialValue_FP r hr)
  exact E.congr (funext fun q => by
    have ho := ArithmeticBits.one_residueBits (mValue q)
    by_cases he : Nat.fromBitsLE (selectedDegree q) = r (context q)
    · simp only [monomialValue, he, ite_true, PrimitivePairBits.coefficient, Polynomial.coeff_X_pow,
        coefficientResidue, Int.cast_one]
      simpa only [mValue, BinaryNat.succ_eq_bits, BinaryNatCode.encode] using ho
    · simp only [monomialValue, he, ite_false, PrimitivePairBits.coefficient, Polynomial.coeff_X_pow,
        coefficientResidue, Int.cast_zero, MatrixPower.residueBits, ZMod.val_zero,
        BinaryNatCode.encode, Nat.zero_bits])

noncomputable def value (n d : List Bool → ℤ[X]) (e r j : List Bool → ℕ) (modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  coefficientResidue
    ((clear (e c) (X ^ r c) (n c) (d c)).coeff (j c)) (Nat.fromBitsLE (modulus c) + 1)

theorem evaluator (n d : List Bool → ℤ[X]) (e r j : List Bool → ℕ) (modulus : List Bool → List Bool)
    (he : BinaryFn e) (hr : BinaryFn r) (hj : BinaryFn j) (hm : modulus ∈ FP)
    (N : SpaceFunction (PrimitivePairBits.coefficient n)) (D : SpaceFunction (PrimitivePairBits.coefficient d)) :
    SpaceFunction (value n d e r j modulus) := by
  have E := UnivariateRationalBits.evaluator (fun c => (X : ℤ[X]) ^ r c) n d e he (monomialEvaluator r hr) N D
  have hq := mem_FP_pair (mem_FP_pair id_mem_FP hj.bits_mem_FP) hm
  have R := E.precompose (fun c => pair (pair c (BinaryNatCode.encode (j c))) (modulus c)) hq
  exact R.congr (funext fun c => by
    simp only [Function.comp_apply, PrimitivePairBits.coefficient, context, selectedDegree, mValue,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl)

end LeanCanny.Algebra.ClearingMatrixBits
