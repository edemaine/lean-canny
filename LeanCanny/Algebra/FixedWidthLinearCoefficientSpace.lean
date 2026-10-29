/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthBlockRenameSpace
public import LeanCanny.Algebra.ModularAddFP
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Native coefficients of coordinate variables and copy constraints

A bounded exponent scan recognizes the monomial X_i. Two such readers and
native modular subtraction read X_i-X_j, including coincident coordinates,
zero-width exponent layouts, redundant bits, and modulus one.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthLinearCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial MatrixPower MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (A W selected : List Bool → ℕ) (target modulus : List Bool → List Bool)

def Matches (c : List Bool) : Prop := selected c < A c ∧ ∀ i < A c,
  FixedWidthQuery.coordinate W target c i = if i = selected c then 1 else 0

theorem matches_FP (hA : UnaryFn A) (hW : UnaryFn W) (hs : BinaryFn selected) (ht : target ∈ FP) :
    FPPred (Matches A W selected target) := by
  have hi := BinaryFn.ofUnary UnaryFn.index
  have he := hi.eq (hs.comp pairFst_mem_FP)
  have hc := BinaryFn.fromBits (take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP ht)
    (UnaryFn.index.mul hW.lift)) hW.lift)
  have hp := (he.and (hc.eq (BinaryFn.const 1))).or (he.not.and (hc.eq (BinaryFn.const 0)))
  have hall := FPPred.forall_lt hA hp
  apply ((hs.lt (BinaryFn.ofUnary hA)).and hall).of_iff
  intro c
  simp only [Matches, Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate,
    FixedWidthQuery.coordinate]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro _
  by_cases h : i = selected c <;> simp [h]

noncomputable def value (c : List Bool) : List Bool :=
  if Matches A W selected target c then ArithmeticBits.one (modulus c) else []

theorem value_FP (hA : UnaryFn A) (hW : UnaryFn W) (hs : BinaryFn selected) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    value A W selected target modulus ∈ FP :=
  (matches_FP A W selected target hA hW hs ht).ite_mem_FP
    (mem_FP_comp (g := ArithmeticBits.one) hm ArithmeticBits.one_mem_FP) (constFn_mem_FP [])

theorem matches_iff (c : List Bool) (i : Fin (A c)) (hi : selected c = i.val) :
    Matches A W selected target c ↔
      nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c)) = Finsupp.single i 1 := by
  have he (j : Fin (A c)) :
      nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c)) j =
        FixedWidthQuery.coordinate W target c j.val := FixedWidthBlockRenameBits.entry_bits _ _ _
  constructor
  · rintro ⟨_, h⟩
    ext j
    rw [he]
    simpa only [hi, Finsupp.single_apply, Fin.ext_iff, eq_comm] using h j.val j.isLt
  · intro h
    refine ⟨by rw [hi]; exact i.isLt, ?_⟩
    intro j hj
    have H := congrArg (fun m : Fin (A c) →₀ ℕ => m ⟨j, hj⟩) h
    simpa only [he, hi, Finsupp.single_apply, Fin.ext_iff, eq_comm] using H

theorem packet (c : List Bool) (i : Fin (A c)) (hi : selected c = i.val) (m : ℕ)
    (hm : modulus c = BinaryNatCode.encode m) : value A W selected target modulus c =
      residueBits (((X i : MvPolynomial (Fin (A c)) ℤ).coeff
        (nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c))) : ℤ) : ZMod m) := by
  rw [value, coeff_X, matches_iff A W selected target c i hi]
  by_cases he : nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c)) = Finsupp.single i 1
  · rw [ite_eq_left he, ite_eq_left he.symm, hm, ArithmeticBits.one_residueBits]
    simp only [Int.cast_one]
  · rw [ite_eq_right he, ite_eq_right (fun h => he h.symm)]
    simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode]
    rfl

noncomputable def difference (old : List Bool → ℕ) (c : List Bool) : List Bool :=
  ArithmeticBits.addMod (pair (modulus c) (pair (value A W selected target modulus c)
    (ArithmeticBits.negate (pair (modulus c) (value A W old target modulus c)))))

attribute [local irreducible] value ArithmeticBits.addMod ArithmeticBits.negate

theorem difference_FP {old : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W)
    (hs : BinaryFn selected) (ho : BinaryFn old) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    difference A W selected target modulus old ∈ FP := by
  have hl := value_FP A W selected target modulus hA hW hs ht hm
  have hr := value_FP A W old target modulus hA hW ho ht hm
  have hn := mem_FP_comp (g := ArithmeticBits.negate) (mem_FP_pair hm hr) ArithmeticBits.negate_mem_FP
  exact mem_FP_comp (g := ArithmeticBits.addMod) (mem_FP_pair hm (mem_FP_pair hl hn)) ArithmeticBits.addMod_mem_FP

theorem difference_packet (old : List Bool → ℕ) (c : List Bool) (i j : Fin (A c))
    (hi : selected c = i.val) (hj : old c = j.val) (m : ℕ) [NeZero m]
    (hm : modulus c = BinaryNatCode.encode m) : difference A W selected target modulus old c =
      residueBits ((((X i - X j : MvPolynomial (Fin (A c)) ℤ).coeff
        (nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c)))) : ℤ) : ZMod m) := by
  rw [difference, packet A W selected target modulus c i hi m hm, packet A W old target modulus c j hj m hm,
    hm, ArithmeticBits.negate_residueBits, ArithmeticBits.addMod_residueBits]
  apply congrArg (fun z : ZMod m => residueBits z)
  rw [← sub_eq_add_neg, ← Int.cast_sub]
  rfl

end LeanCanny.Algebra.FixedWidthLinearCoefficientBits
