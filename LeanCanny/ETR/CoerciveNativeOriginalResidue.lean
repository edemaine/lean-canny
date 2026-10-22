/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveAnnihilatorResidue
public import LeanCanny.ETR.CoerciveNativeAnnihilators

/-! # Native residues for every actual coercive leaf, including the pin -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveNativeOriginalResidue
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ArithmeticBits.one ArithmeticBits.negate BinaryNat.succ BinaryNat.sub

private lemma eqCodeFP {f : List Bool → List Bool} (hf : f ∈ FP) (k : ℕ) :
    FPPred (fun c => Nat.fromBitsLE (f c) = k) :=
  ((BinaryNat.le_fppred hf (constFn_mem_FP (BinaryNatCode.encode k))).and
    (BinaryNat.le_fppred (constFn_mem_FP (BinaryNatCode.encode k)) hf)).of_iff
      (fun _ => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)

def pinProgram (rootDegree parameterDegree modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  if Nat.fromBitsLE (rootDegree c) = 1 ∧ Nat.fromBitsLE (parameterDegree c) = 0 then
    ArithmeticBits.one (BinaryNat.succ (modulus c))
  else if Nat.fromBitsLE (rootDegree c) = 0 ∧ Nat.fromBitsLE (parameterDegree c) = 1 then
    ArithmeticBits.negate (pair (BinaryNat.succ (modulus c)) (ArithmeticBits.one (BinaryNat.succ (modulus c)))) else []

lemma pinProgram_FP {rootDegree parameterDegree modulus : List Bool → List Bool}
    (hr : rootDegree ∈ FP) (hp : parameterDegree ∈ FP) (hm : modulus ∈ FP) : pinProgram rootDegree parameterDegree modulus ∈ FP := by
  have hmod := mem_FP_comp hm BinaryNat.succ_mem_FP
  have hone := mem_FP_comp hmod ArithmeticBits.one_mem_FP
  have hneg := mem_FP_comp (mem_FP_pair hmod hone) ArithmeticBits.negate_mem_FP
  exact mem_FP_of_eq (((eqCodeFP hr 1).and (eqCodeFP hp 0)).ite_mem_FP hone
    (((eqCodeFP hr 0).and (eqCodeFP hp 1)).ite_mem_FP hneg (constFn_mem_FP []))) (fun _ => rfl)

lemma pin_coeff (k l : ℕ) : ((CoerciveNativeAnnihilators.pin.coeff k).coeff l) =
    (if k = 1 ∧ l = 0 then (1 : ℤ) else 0) - (if k = 0 ∧ l = 1 then 1 else 0) := by
  by_cases hk0 : k = 0 <;> by_cases hk1 : k = 1 <;>
    by_cases hl0 : l = 0 <;> by_cases hl1 : l = 1 <;>
      simp [CoerciveNativeAnnihilators.pin, Polynomial.coeff_X, Polynomial.coeff_C,
        Polynomial.coeff_one, hk0, hk1, hl0, hl1, eq_comm]

noncomputable def pinCoefficient (rootDegree parameterDegree modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  let a : ℤ := (CoerciveNativeAnnihilators.pin.coeff (Nat.fromBitsLE (rootDegree c))).coeff
    (Nat.fromBitsLE (parameterDegree c))
  residueBits (a : ZMod (Nat.fromBitsLE (modulus c) + 1))

lemma pinProgram_eq (rootDegree parameterDegree modulus : List Bool → List Bool) (c : List Bool) :
    pinProgram rootDegree parameterDegree modulus c = pinCoefficient rootDegree parameterDegree modulus c := by
  let m := Nat.fromBitsLE (modulus c) + 1
  let : NeZero m := ⟨by dsimp [m]; omega⟩
  have hmod : BinaryNat.succ (modulus c) = BinaryNatCode.encode m := by rw [BinaryNat.succ_eq_bits]; rfl
  rw [pinCoefficient, pin_coeff]
  by_cases hplus : Nat.fromBitsLE (rootDegree c) = 1 ∧ Nat.fromBitsLE (parameterDegree c) = 0
  · have hminus : ¬(Nat.fromBitsLE (rootDegree c) = 0 ∧ Nat.fromBitsLE (parameterDegree c) = 1) := by omega
    simp only [pinProgram, ite_eq_left hplus, ite_eq_right hminus, sub_zero, Int.cast_one]
    rw [hmod, ArithmeticBits.one_residueBits]
  · by_cases hminus : Nat.fromBitsLE (rootDegree c) = 0 ∧ Nat.fromBitsLE (parameterDegree c) = 1
    · simp only [pinProgram, ite_eq_right hplus, ite_eq_left hminus, zero_sub, Int.cast_neg, Int.cast_one]
      rw [hmod, ArithmeticBits.one_residueBits, ArithmeticBits.negate_residueBits]
    · simp only [pinProgram, ite_eq_right hplus, ite_eq_right hminus, sub_self, Int.cast_zero]
      simp [residueBits, BinaryNatCode.encode]

noncomputable def coefficient (input index rootDegree parameterDegree modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits (((((CoerciveNativeAnnihilators.original (input c) (Nat.fromBitsLE (index c))).coeff
    (Nat.fromBitsLE (rootDegree c))).coeff (Nat.fromBitsLE (parameterDegree c))) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus c) + 1))

/-- Every leaf coefficient comes from the actual encoded source. -/
theorem evaluator {input index rootDegree parameterDegree modulus : List Bool → List Bool}
    (hi : input ∈ FP) (hj : index ∈ FP) (hr : rootDegree ∈ FP) (hp : parameterDegree ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (coefficient input index rootDegree parameterDegree modulus) := by
  let predecessor := fun c => BinaryNat.sub (pair (index c) (BinaryNatCode.encode 1))
  have hpred : predecessor ∈ FP := mem_FP_comp (mem_FP_pair hj (constFn_mem_FP _)) BinaryNat.sub_mem_FP
  have ES := CoerciveAnnihilatorResidue.coefficientEvaluator hi hpred hr hp hm
  have EP := SpaceFunction.ofFP _ (mem_FP_of_eq (pinProgram_FP hr hp hm) (pinProgram_eq rootDegree parameterDegree modulus))
  have EB := SpaceFunction.branch (fun c => decide (Nat.fromBitsLE (index c) = 0))
    (eqCodeFP hj 0).flag_mem_FP EP ES
  refine EB.congr (funext fun c => ?_)
  simp only [decide_eq_true_eq]
  cases h : Nat.fromBitsLE (index c) with
  | zero => simp only [h, ite_true, coefficient, CoerciveNativeAnnihilators.original, pinCoefficient]
  | succ i =>
    simp only [h, Nat.add_one_ne_zero, ite_false, CoerciveAnnihilatorResidue.coefficient,
      coefficient, CoerciveNativeAnnihilators.original, predecessor, BinaryNat.sub_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.add_sub_cancel]

end LeanCanny.ETR.CoerciveNativeOriginalResidue
