/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthRowArithmetic

/-! # Native original rows with polynomial constant shifts

The integer row reader and the shift's parameter coefficient reader are both
charged. A zero parameter-index guard lifts the integer row; a zero spatial
exponent guard handles the shift. No homogeneous-row reader is an input.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialParameterShiftBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def value (N W : List Bool → ℕ)
    (p : (c : List Bool) → MvPolynomial (Fin (N c)) ℤ) (s : List Bool → Polynomial ℤ)
    (target parameter modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits ((((((p c).map Polynomial.C - C (s c)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W c) (Nat.fromBitsLE (target c)))).coeff
      (Nat.fromBitsLE (parameter c))) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))

noncomputable def scalar (s : List Bool → Polynomial ℤ) (parameter modulus : List Bool → List Bool)
    (c : List Bool) : List Bool :=
  residueBits (((s c).coeff (Nat.fromBitsLE (parameter c)) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))

theorem evaluator {N W : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W)
    (p : (c : List Bool) → MvPolynomial (Fin (N c)) ℤ) (s : List Bool → Polynomial ℤ)
    (target parameter modulus : List Bool → List Bool)
    (ht : target ∈ FP) (hk : parameter ∈ FP) (hm : modulus ∈ FP)
    (EP : SpaceFunction (FixedWidthRowBits.value N W p target modulus))
    (ES : SpaceFunction (scalar s parameter modulus)) :
    SpaceFunction (value N W p s target parameter modulus) := by
  have hz := (BinaryFn.fromBits hk).eq (BinaryFn.const 0)
  have EZ : SpaceFunction (FixedWidthRowBits.value N W (fun _ => 0) target modulus) := by
    refine (SpaceFunction.ofFP _ (constFn_mem_FP [])).congr (funext fun c => ?_)
    simp [FixedWidthRowBits.value, residueBits, BinaryNatCode.encode]
  have EL := FixedWidthRowBits.branch_evaluator N W p (fun _ => 0) target modulus
    (fun c => Nat.fromBitsLE (parameter c) = 0) hz EP EZ
  have EC := FixedWidthConstantBits.evaluator hN hW ht ES
    (fun c => (s c).coeff (Nat.fromBitsLE (parameter c))) (fun _ => rfl)
  have E := FixedWidthRowBits.sub_evaluator N W
    (fun c => if Nat.fromBitsLE (parameter c) = 0 then p c else 0)
    (fun c => C ((s c).coeff (Nat.fromBitsLE (parameter c)))) target modulus hm EL EC
  refine E.congr (funext fun c => ?_)
  simp only [FixedWidthRowBits.value, value, coeff_sub, coeff_map, coeff_C, Polynomial.coeff_sub]
  by_cases hp : Nat.fromBitsLE (parameter c) = 0
  · simp only [hp, ite_true, Polynomial.coeff_C]
    split_ifs <;> rfl
  · simp only [hp, ite_false, AddMonoidAlgebra.coeff_zero, Polynomial.coeff_C]
    split_ifs <;> simp

end LeanCanny.Algebra.PolynomialParameterShiftBits
