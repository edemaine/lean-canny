/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialParameterShiftSpace

/-! # Native coefficients of one selected parameter shift -/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialParameterShiftBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

theorem singleScalarEvaluator (row height : List Bool → ℕ) (hr : UnaryFn row) (hh : UnaryFn height)
    (parameter modulus : List Bool → List Bool) (hk : parameter ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (scalar (fun q => if row q = height q then Polynomial.X else 0) parameter modulus) := by
  have hs := ((BinaryFn.ofUnary hr).eq (BinaryFn.ofUnary hh)).and
    ((BinaryFn.fromBits hk).eq (BinaryFn.const 1))
  have E1 := SpaceFunction.ofFP _ (mem_FP_comp (mem_FP_comp hm BinaryNat.succ_mem_FP) ArithmeticBits.one_mem_FP)
  have E := SpaceFunction.branch (fun q => decide (row q = height q ∧ Nat.fromBitsLE (parameter q) = 1))
    hs.flag_mem_FP E1 (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine E.congr (funext fun q => ?_)
  simp only [scalar, decide_eq_true_eq, Function.comp_apply]
  by_cases he : row q = height q
  · simp only [he, ite_true, true_and, Polynomial.coeff_X, eq_comm (a := (1 : ℕ))]
    split_ifs
    · rw [BinaryNat.succ_eq_bits]
      exact ArithmeticBits.one_residueBits _
    · simp [residueBits, BinaryNatCode.encode]
  · simp [he, residueBits, BinaryNatCode.encode]

end LeanCanny.Algebra.PolynomialParameterShiftBits
