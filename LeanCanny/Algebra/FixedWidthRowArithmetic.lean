/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineIntegerSpace
public import LeanCanny.Algebra.FixedWidthConstantSpace
public import LeanCanny.Computation.SpaceFunctionSelect

/-! # Native arithmetic and branching for integer polynomial row readers -/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthRowBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def value (A W : List Bool → ℕ) (p : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ)
    (target modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits (((p c).coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (A c)))
    (W c) (Nat.fromBitsLE (target c))) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))

def finish (negative : Bool) (modulus : List Bool → List Bool) (z : List Bool) : List Bool :=
  ArithmeticBits.addMod (pair (FlatAffineIntegerSpace.modulusCode modulus (pairFst z))
    (pair (pairFst (pairSnd z)) (if negative then
      ArithmeticBits.negate (pair (FlatAffineIntegerSpace.modulusCode modulus (pairFst z)) (pairSnd (pairSnd z)))
      else pairSnd (pairSnd z))))

attribute [local irreducible] ArithmeticBits.addMod ArithmeticBits.negate

theorem finish_FP (negative : Bool) {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : finish negative modulus ∈ FP := by
  have hM := mem_FP_comp pairFst_mem_FP (FlatAffineIntegerSpace.modulusCode_FP modulus hm)
  have hl := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hr := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  cases negative with
  | false => exact mem_FP_comp (mem_FP_pair hM (mem_FP_pair hl hr)) ArithmeticBits.addMod_mem_FP
  | true =>
    have hn := mem_FP_comp (mem_FP_pair hM hr) ArithmeticBits.negate_mem_FP
    exact mem_FP_comp (mem_FP_pair hM (mem_FP_pair hl hn)) ArithmeticBits.addMod_mem_FP

theorem combine_evaluator (negative : Bool) (A W : List Bool → ℕ)
    (p q : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ) (target modulus : List Bool → List Bool)
    (hm : modulus ∈ FP) (hp : SpaceFunction (value A W p target modulus))
    (hq : SpaceFunction (value A W q target modulus)) :
    SpaceFunction (value A W (fun c => p c + if negative then -q c else q c) target modulus) := by
  have H := (hp.pairOutputs hq).withInput.postcompose (finish negative modulus) (finish_FP negative hm)
  refine H.congr (funext fun c => ?_)
  change finish negative modulus (pair c (pair (value A W p target modulus c) (value A W q target modulus c))) = _
  unfold finish
  simp only [pairFst_pair, pairSnd_pair]
  rw [FlatAffineIntegerSpace.modulusCode_eq]
  unfold value
  cases negative with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [ArithmeticBits.addMod_residueBits]
    apply congrArg residueBits
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Int.cast_add]
  | true =>
    simp only [ite_true]
    rw [ArithmeticBits.negate_residueBits, ArithmeticBits.addMod_residueBits]
    apply congrArg residueBits
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_neg, Int.cast_add, Int.cast_neg]

theorem add_evaluator (A W : List Bool → ℕ) (p q : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ)
    (target modulus : List Bool → List Bool) (hm : modulus ∈ FP)
    (hp : SpaceFunction (value A W p target modulus)) (hq : SpaceFunction (value A W q target modulus)) :
    SpaceFunction (value A W (fun c => p c + q c) target modulus) := combine_evaluator false A W p q target modulus hm hp hq

theorem sub_evaluator (A W : List Bool → ℕ) (p q : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ)
    (target modulus : List Bool → List Bool) (hm : modulus ∈ FP)
    (hp : SpaceFunction (value A W p target modulus)) (hq : SpaceFunction (value A W q target modulus)) :
    SpaceFunction (value A W (fun c => p c - q c) target modulus) := by
  simpa only [sub_eq_add_neg, ite_true] using combine_evaluator true A W p q target modulus hm hp hq

theorem branch_evaluator (A W : List Bool → ℕ) (p q : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ)
    (target modulus : List Bool → List Bool) (pred : List Bool → Prop) [DecidablePred pred]
    (hpred : FPPred pred) (hp : SpaceFunction (value A W p target modulus))
    (hq : SpaceFunction (value A W q target modulus)) :
    SpaceFunction (value A W (fun c => if pred c then p c else q c) target modulus) := by
  have H := SpaceFunction.branch (fun c => decide (pred c)) hpred.flag_mem_FP hp hq
  exact H.congr (funext fun c => by
    by_cases hc : pred c <;> simp only [value, hc, decide_eq_true_eq, ite_true, ite_false])

theorem select_evaluator (A W : List Bool → ℕ) (p q : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ)
    (target modulus pred : List Bool → List Bool) (hpred : SpaceFunction pred)
    (hp : SpaceFunction (value A W p target modulus)) (hq : SpaceFunction (value A W q target modulus)) :
    SpaceFunction (value A W (fun c => if (pred c)[0]?.getD false then p c else q c) target modulus) := by
  have H := SpaceFunction.select hpred hp hq
  exact H.congr (funext fun c => by
    cases hc : (pred c)[0]?.getD false <;> simp only [value, hc, Bool.false_eq_true, ite_true, ite_false])

theorem guarded_evaluator (A W : List Bool → ℕ) (p : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ)
    (target modulus program : List Bool → List Bool) (pred : List Bool → Prop) [DecidablePred pred]
    (hpred : FPPred pred) (hp : SpaceFunction program)
    (hpacket : ∀ c, pred c → program c = value A W p target modulus c) :
    SpaceFunction (value A W (fun c => if pred c then p c else 0) target modulus) := by
  have H := SpaceFunction.branch (fun c => decide (pred c)) hpred.flag_mem_FP hp (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine H.congr (funext fun c => ?_)
  by_cases hc : pred c
  · simp only [decide_eq_true_eq, hc, ite_true, hpacket c hc]
    simp only [value, hc, ite_true]
  · simp only [decide_eq_true_eq, hc, ite_false, value, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, Int.cast_zero,
      residueBits, ZMod.val_zero, BinaryNatCode.encode]
    rfl

theorem variable_evaluator (A W : List Bool → ℕ) (selected : (c : List Bool) → Fin (A c))
    (target modulus : List Bool → List Bool) (hA : UnaryFn A) (hW : UnaryFn W)
    (hs : UnaryFn (fun c => (selected c).val)) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value A W (fun c => X (selected c)) target modulus) := by
  have H := SpaceFunction.ofFP _ (FixedWidthLinearCoefficientBits.value_FP A W (fun c => (selected c).val) target
    (FlatAffineIntegerSpace.modulusCode modulus) hA hW (BinaryFn.ofUnary hs) ht
      (FlatAffineIntegerSpace.modulusCode_FP modulus hm))
  exact H.congr (funext fun c => FixedWidthLinearCoefficientBits.packet A W _ target _ c (selected c) rfl
    (Nat.fromBitsLE (modulus c) + 1) (FlatAffineIntegerSpace.modulusCode_eq modulus c))

end LeanCanny.Algebra.FixedWidthRowBits
