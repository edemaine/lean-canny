/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialPseudoRemainderSpace

/-! # Certified bivariate readers for fixed polynomial reductions

Out-of-range outer coefficients return zero. The resulting reader has the
same original-context, modulus, inner-index, outer-index interface as its
two inputs, and can feed subsequent degree and principal-sign queries.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialPseudoRemainderBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

def valid (F : Family) (z : List Bool) : Prop := index z < F.bound (origin z) + 1
instance (F : Family) (z : List Bool) : Decidable (valid F z) := inferInstanceAs (Decidable (_ < _))

theorem valid_fppred {F : Family} (A : Access F) : FPPred (valid F) := by
  have hi : BinaryFn index := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have hb : BinaryFn (fun z => F.bound (origin z) + 1) :=
    BinaryFn.add (A.bound.comp origin_FP) (BinaryFn.const 1)
  exact hi.lt hb

noncomputable def value (F : Family) (z : List Bool) : List Bool :=
  if valid F z then (moment F).value z else []

theorem evaluator {F : Family} (A : Access F) : SpaceFunction (value F) := by
  have E := SpaceFunction.branch (fun z => decide (valid F z)) (valid_fppred A).flag_mem_FP
    (moment_evaluator A) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun z => by simp only [value, decide_eq_true_eq])

theorem value_eq (F : Family) (z : List Bool) :
    value F z = residueBits ((((F.reduced (origin z)).coeff (index z)).coeff (parameter z) : ℤ) : ZMod (modulus z)) := by
  by_cases hv : valid F z
  · have hs : (selected F z).val = index z := Nat.mod_eq_of_lt hv
    rw [value, ite_eq_left hv, moment_value, hs]
  · have hz : (F.reduced (origin z)).coeff (index z) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hd := F.reduced_degree (origin z)
      unfold valid at hv
      omega
    rw [value, ite_eq_right hv, hz, Polynomial.coeff_zero, Int.cast_zero]
    simp [residueBits, BinaryNatCode.encode]

noncomputable def reader {F : Family} (A : Access F) : CertifiedPolynomial.BivariateReader F.reduced where
  coefficient := value F
  evaluator := evaluator A
  coefficient_eq q u v := by
    rw [value_eq]
    exact congrArg₂ (fun (a : ℤ) (n : ℕ) => residueBits (a : ZMod n))
      (by simp only [origin, index, parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
      (by simp only [modulus, pairFst_pair])

end LeanCanny.Algebra.PolynomialPseudoRemainderBits
