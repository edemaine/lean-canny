/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralFrozenPowerSumSpace
public import LeanCanny.Algebra.ModularPowFP

/-! # Native frozen Fermat constant coefficients

An integer leading-coefficient residue scales the constructed frozen-power
sum. A bounded free-exponent guard selects exactly the constant monomial.
Only the original height and integer-leading readers are supplied.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralFrozenPowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Source.leadingValue (S : Source) (c : List Bool) : List Bool := by
  letI := S.ring c
  exact residueBits ((Algebra.leftMulMatrix (S.basis c)
    ((S.leading c : S.carrier c) * CoordinateBlockSpecialization.frozenPower (n := S.arity c)
      (S.height c) (S.offset c) (S.free c) (S.allowance c)) (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c))

theorem leading_value (S : Source) (c : List Bool) :
    letI := S.ring c
    residueBits ((S.leading c : ZMod (S.modulus c)) *
      ((Algebra.leftMulMatrix (S.basis c)
        (CoordinateBlockSpecialization.frozenPower (n := S.arity c) (S.height c) (S.offset c) (S.free c) (S.allowance c))
        (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c))) = S.leadingValue c := by
  let := S.ring c
  let F := CoordinateBlockSpecialization.frozenPower (n := S.arity c) (S.height c) (S.offset c) (S.free c) (S.allowance c)
  have H : Algebra.leftMulMatrix (S.basis c) ((S.leading c : S.carrier c) * F) (S.row c) (S.col c) =
      S.leading c * Algebra.leftMulMatrix (S.basis c) F (S.row c) (S.col c) := by
    rw [← zsmul_eq_mul, map_zsmul, Matrix.smul_apply, zsmul_eq_mul]
    simp only [Int.cast_id]
  unfold Source.leadingValue
  rw [H, Int.cast_mul]

def multiplyPost (S : Source) (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (BinaryNatCode.encode (S.modulus (pairFst z))) (pairSnd z))

theorem multiplyPost_FP (S : Source) (a : Access S) : multiplyPost S ∈ FP := by
  have HM : BinaryFn (fun z => S.modulus (pairFst z)) := a.modulus.comp pairFst_mem_FP
  exact mem_FP_comp (mem_FP_pair HM.bits_mem_FP pairSnd_mem_FP) BinaryNat.mulMod_mem_FP

theorem multiplyPost_packet (S : Source) (c : List Bool) (x y : ZMod (S.modulus c)) :
    multiplyPost S (pair c (pair (residueBits x) (residueBits y))) = residueBits (x * y) := by
  simp only [multiplyPost, pairFst_pair, pairSnd_pair]
  exact ArithmeticBits.mulMod_residueBits _ x y

theorem leading_evaluator (S : Source) (a : Access S) (EH : SpaceFunction a.height) (EA : SpaceFunction a.leading) :
    SpaceFunction S.leadingValue := by
  have E := ((EA.pairOutputs (sum_evaluator S a EH)).withInput).postcompose (multiplyPost S) (multiplyPost_FP S a)
  refine E.congr (funext fun c => ?_)
  change multiplyPost S (pair c (pair (a.leading c) (S.sumValue c))) = _
  rw [a.leading_eq, Source.sumValue, multiplyPost_packet]
  exact leading_value S c

def zeroTarget (S : Source) (c : List Bool) : Prop :=
  FixedWidthQuery.Bounded S.free S.targetWidth (fun z => BinaryNatCode.encode (S.target z)) (fun _ => 0) c

theorem zeroTarget_fppred (S : Source) (a : Access S) : FPPred (zeroTarget S) :=
  FixedWidthQuery.bounded_binary_fppred a.free a.targetWidth (BinaryFn.const 0) a.target.bits_mem_FP

theorem zeroTarget_eq (S : Source) (c : List Bool) : zeroTarget S c ↔ S.toSource.targetExponent c = 0 := by
  have HE (i : ℕ) : FixedWidthQuery.coordinate S.targetWidth (fun z => BinaryNatCode.encode (S.target z)) c i =
      FixedWidthPolynomial.entry (S.targetWidth c) (S.target c) i := by
    rw [FixedWidthQuery.coordinate_eq_entry, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  constructor
  · intro h
    apply Finsupp.ext
    intro i
    have H := h i.val i.isLt
    rw [HE] at H
    exact Nat.eq_zero_of_le_zero H
  · intro h i hi
    have H := congrArg (fun e : Fin (S.free c) →₀ ℕ => e ⟨i, hi⟩) h
    rw [HE]
    exact (show FixedWidthPolynomial.entry (S.targetWidth c) (S.target c) i = 0 from H).le

noncomputable def Source.constantValue (S : Source) (c : List Bool) : List Bool := by
  letI := S.ring c
  exact residueBits ((Algebra.leftMulMatrix (S.basis c)
    ((MvPolynomial.C ((S.leading c : S.carrier c) * CoordinateBlockSpecialization.frozenPower (n := S.arity c)
      (S.height c) (S.offset c) (S.free c) (S.allowance c)) : MvPolynomial (Fin (S.free c)) (S.carrier c)).coeff
        (S.toSource.targetExponent c)) (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c))

theorem constant_value (S : Source) (c : List Bool) :
    (if zeroTarget S c then S.leadingValue c else []) = S.constantValue c := by
  let := S.ring c
  unfold Source.constantValue
  rw [MvPolynomial.coeff_C]
  by_cases h : S.toSource.targetExponent c = 0
  · rw [ite_eq_left ((zeroTarget_eq S c).mpr h), ite_eq_left h.symm]
    rfl
  · rw [ite_eq_right (fun H => h ((zeroTarget_eq S c).mp H)), ite_eq_right (Ne.symm h)]
    simp only [map_zero, Matrix.zero_apply, Int.cast_zero, residueBits, ZMod.val_zero,
      BinaryNatCode.encode, Nat.zero_bits]

attribute [local irreducible] Source.leadingValue Source.constantValue

theorem constant_evaluator (S : Source) (a : Access S) (EH : SpaceFunction a.height) (EA : SpaceFunction a.leading) :
    SpaceFunction S.constantValue := by
  refine (SpaceFunction.branch (fun c => decide (zeroTarget S c)) (zeroTarget_fppred S a).flag_mem_FP
    (leading_evaluator S a EH EA) (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr ?_
  funext c
  simp only [decide_eq_true_eq]
  exact constant_value S c

end LeanCanny.Algebra.IntegralFrozenPowerBits
