/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogenizationPolynomialSpace
public import LeanCanny.Algebra.FixedWidthRowArithmetic

/-! # Native coefficients of the reciprocal coordinate row T Xᵢ - X₀ -/

@[expose] public section
namespace LeanCanny.Algebra.ReciprocalCoordinateBits
open LeanCanny.Encoding LeanCanny.Computation MvPolynomial MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (N : List Bool → ℕ) (coordinate : (c : List Bool) → Fin (N c))
    (c : List Bool) : MvPolynomial (Fin (N c + 1)) (Polynomial ℤ) :=
  C Polynomial.X * X (coordinate c).succ - X 0

lemma coefficient (n : ℕ) (i : Fin (n + 1)) (m : Fin (n + 1) →₀ ℕ) (j : ℕ) :
    (((C Polynomial.X * X i - X 0 : MvPolynomial (Fin (n + 1)) (Polynomial ℤ)).coeff m).coeff j) =
      if j = 0 then -((X 0 : MvPolynomial (Fin (n + 1)) ℤ).coeff m)
      else if j = 1 then (X i : MvPolynomial (Fin (n + 1)) ℤ).coeff m else 0 := by
  simp only [coeff_sub, coeff_C_mul, coeff_X]
  split_ifs <;> simp_all [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_one] <;> omega

noncomputable def value (N W : List Bool → ℕ) (coordinate : (c : List Bool) → Fin (N c))
    (parameter modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  residueBits (((polynomial N coordinate (pairFst q)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W (pairFst q)) (Nat.fromBitsLE (pairSnd q)))).coeff
      (Nat.fromBitsLE (parameter (pairFst q))) : ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1))

theorem evaluator {N W : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W)
    (coordinate : (c : List Bool) → Fin (N c)) (hc : UnaryFn (fun c => (coordinate c).val))
    {parameter modulus : List Bool → List Bool} (hk : parameter ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value N W coordinate parameter modulus) := by
  let A := fun q => N (pairFst q) + 1
  let V := W ∘ pairFst
  let selected : (q : List Bool) → Fin (A q) := fun q => (coordinate (pairFst q)).succ
  let zero : (q : List Bool) → Fin (A q) := fun _ => 0
  have hA : UnaryFn A := (hN.comp pairFst_mem_FP).add (UnaryFn.const 1)
  have hV : UnaryFn V := hW.comp pairFst_mem_FP
  have hM := mem_FP_comp pairFst_mem_FP hm
  have Ei := FixedWidthRowBits.variable_evaluator A V selected pairSnd (modulus ∘ pairFst) hA hV
    ((hc.comp pairFst_mem_FP).add (UnaryFn.const 1)) pairSnd_mem_FP hM
  have E0 := FixedWidthRowBits.variable_evaluator A V zero pairSnd (modulus ∘ pairFst) hA hV
    (UnaryFn.const 0) pairSnd_mem_FP hM
  have Ez : SpaceFunction (FixedWidthRowBits.value A V (fun _ => 0) pairSnd (modulus ∘ pairFst)) := by
    refine (SpaceFunction.ofFP _ (constFn_mem_FP [])).congr (funext fun q => ?_)
    simp [FixedWidthRowBits.value, residueBits, BinaryNatCode.encode]
  have En := FixedWidthRowBits.sub_evaluator A V _ _ pairSnd (modulus ∘ pairFst) hM Ez E0
  have Ep : BinaryFn (fun q => Nat.fromBitsLE (parameter (pairFst q))) := (BinaryFn.fromBits hk).comp pairFst_mem_FP
  have E1 := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (parameter (pairFst q)) = 1))
    (Ep.eq (BinaryFn.const 1)).flag_mem_FP Ei (SpaceFunction.ofFP _ (constFn_mem_FP []))
  have E := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (parameter (pairFst q)) = 0))
    (Ep.eq (BinaryFn.const 0)).flag_mem_FP En E1
  refine E.congr (funext fun q => ?_)
  simp only [value, polynomial, coefficient]
  by_cases h0 : Nat.fromBitsLE (parameter (pairFst q)) = 0
  · simp only [h0, decide_eq_true_eq, ite_true, FixedWidthRowBits.value, zero_sub]
    rfl
  · by_cases h1 : Nat.fromBitsLE (parameter (pairFst q)) = 1
    · simp only [h1, decide_eq_true_eq, ite_true, FixedWidthRowBits.value]
      rfl
    · simp only [h0, h1, decide_eq_true_eq, ite_false, residueBits, ZMod.val_zero, BinaryNatCode.encode, Int.cast_zero]
      rfl

end LeanCanny.Algebra.ReciprocalCoordinateBits
