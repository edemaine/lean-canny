/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthRowArithmetic
public import LeanCanny.Encoding.BinaryDivFP
public import LeanCanny.Algebra.CoordinatePowerCoefficients

/-! # Native coefficient access after coordinate-dependent powers

Each coordinate has its own positive binary power. Divide a requested
exponent by that coordinate’s power. A nonzero remainder rejects the query. Fixed-width
repacking and the divisibility scan are FP; the original reader retains
its full space charge. Arbitrary widths, zero-width blocks, and redundant
input words keep their literal exponent meanings.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthCoordinatePowerBits
open LeanCanny.Encoding LeanCanny.Computation MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (A W power : List Bool → ℕ) (target : List Bool → List Bool)

def division (q : List Bool) : List Bool :=
  BinaryNat.divMod (pair (FixedWidthQuery.read A W target q) (BinaryNatCode.encode (power q)))

lemma division_FP (hA : UnaryFn A) (hW : UnaryFn W) (he : BinaryFn power) (ht : target ∈ FP) :
    division A W power target ∈ FP :=
  mem_FP_comp (mem_FP_pair (FixedWidthQuery.read_mem_FP hA hW ht)
    he.bits_mem_FP) BinaryNat.divMod_mem_FP

lemma division_packet (c : List Bool) (i : ℕ) :
    division A W power target (pair c (BinaryNatCode.encode i)) =
      pair (BinaryNatCode.encode (FixedWidthQuery.entry A W target c i / power (pair c (BinaryNatCode.encode i))))
        (BinaryNatCode.encode (FixedWidthQuery.entry A W target c i % power (pair c (BinaryNatCode.encode i)))) := by
  rw [division, FixedWidthQuery.read_packet, BinaryNat.divMod_pair]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]

def quotientTarget (c : List Bool) : List Bool :=
  FixedWidthNatVector.encode (A c) (W c) (fun i => FixedWidthQuery.entry A W target c i / power (pair c (BinaryNatCode.encode i)))

lemma quotientTarget_FP (hA : UnaryFn A) (hW : UnaryFn W) (he : BinaryFn power) (ht : target ∈ FP) :
    quotientTarget A W power target ∈ FP := by
  apply FixedWidthNatVector.encode_mem_FP A W _ hA hW (fun q => pairFst (division A W power target q))
    (mem_FP_comp (division_FP A W power target hA hW he ht) pairFst_mem_FP)
  intro c i
  rw [division_packet, pairFst_pair]

def Divisible (c : List Bool) : Prop :=
  ∀ i < A c, FixedWidthQuery.entry A W target c i % power (pair c (BinaryNatCode.encode i)) = 0

instance : DecidablePred (Divisible A W power target) := fun _ => inferInstanceAs (Decidable (∀ i < _, _))

lemma divisible_FP (hA : UnaryFn A) (hW : UnaryFn W) (he : BinaryFn power) (ht : target ∈ FP) :
    FPPred (Divisible A W power target) := by
  let loop := fun q => pair (pairFst q) (BinaryNatCode.encode (pairSnd q).length)
  have hl : loop ∈ FP := mem_FP_pair pairFst_mem_FP (bits_mem_FP UnaryFn.index)
  have hr := mem_FP_comp (mem_FP_comp hl (division_FP A W power target hA hW he ht)) pairSnd_mem_FP
  apply ((BinaryNat.eq_const_fppred hr 0).forall_lt hA).of_iff
  intro c
  simp only [Divisible, Function.comp_apply, loop, pairFst_pair, pairSnd_pair, List.length_replicate]
  simp only [division_packet, pairSnd_pair]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]

lemma exponent_coordinate (c : List Bool) (i : Fin (A c)) :
    FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c)) i =
      FixedWidthQuery.coordinate W target c i.val := FixedWidthBlockRenameBits.entry_bits _ _ _

lemma quotient_coordinate (c : List Bool) (i : Fin (A c)) :
    FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (A c))) (W c)
      (Nat.fromBitsLE (quotientTarget A W power target c)) i =
        FixedWidthQuery.coordinate W target c i.val / power (pair c (BinaryNatCode.encode i.val)) := by
  rw [exponent_coordinate]
  change Nat.fromBitsLE (((quotientTarget A W power target c).drop (i.val * W c)).take (W c)) = _
  rw [quotientTarget, FixedWidthNatVector.decode_block _ _ _ i.val i.isLt]
  · simp only [FixedWidthQuery.entry, i.isLt, ite_true]
  · apply (Nat.div_le_self _ _).trans_lt
    unfold FixedWidthQuery.entry
    rw [ite_eq_left i.isLt]
    exact (Nat.fromBitsLE_lt_pow_length _).trans_le
      (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))

lemma coefficient_eq (c : List Bool) (p : MvPolynomial (Fin (A c)) ℤ)
    (he : ∀ i : Fin (A c), 0 < power (pair c (BinaryNatCode.encode i.val))) :
    (CoordinatePowerSubstitution.substitute (fun i : Fin (A c) => power (pair c (BinaryNatCode.encode i.val))) p).coeff
      (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c))) =
      if Divisible A W power target c then p.coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (A c))) (W c)
          (Nat.fromBitsLE (quotientTarget A W power target c))) else 0 := by
  rw [CoordinatePowerSubstitution.coefficient _ he]
  have HQ : CoordinatePowerSubstitution.quotientExponent
      (fun i : Fin (A c) => power (pair c (BinaryNatCode.encode i.val)))
      (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c))) =
      FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (A c))) (W c)
        (Nat.fromBitsLE (quotientTarget A W power target c)) := by
    ext i
    rw [CoordinatePowerSubstitution.quotientExponent_apply, quotient_coordinate, exponent_coordinate]
  rw [HQ]
  have HP : (∀ i : Fin (A c),
      FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c)) i %
        power (pair c (BinaryNatCode.encode i.val)) = 0) ↔ Divisible A W power target c := by
    constructor
    · intro H i hi
      simpa only [exponent_coordinate, FixedWidthQuery.entry, hi, ite_true] using H ⟨i, hi⟩
    · intro H i
      simpa only [exponent_coordinate, FixedWidthQuery.entry, i.isLt, ite_true] using H i.val i.isLt
  simp only [HP]

lemma evaluator (p : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ)
    (modulus : List Bool → List Bool)
    (he : ∀ c (i : Fin (A c)), 0 < power (pair c (BinaryNatCode.encode i.val)))
    (hA : UnaryFn A) (hW : UnaryFn W) (hpower : BinaryFn power) (ht : target ∈ FP)
    (E : SpaceFunction (FixedWidthRowBits.value A W p (quotientTarget A W power target) modulus)) :
    SpaceFunction (FixedWidthRowBits.value A W
      (fun c => CoordinatePowerSubstitution.substitute (fun i : Fin (A c) => power (pair c (BinaryNatCode.encode i.val))) (p c))
      target modulus) := by
  have H := SpaceFunction.branch (fun c => decide (Divisible A W power target c))
    (divisible_FP A W power target hA hW hpower ht).flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine H.congr (funext fun c => ?_)
  simp only [FixedWidthRowBits.value]
  rw [coefficient_eq A W power target c (p c) (he c)]
  by_cases hc : Divisible A W power target c
  · simp only [hc, decide_eq_true_eq, ite_true]
  · simp only [hc, decide_eq_true_eq, ite_false, Int.cast_zero, MatrixPower.residueBits, ZMod.val_zero, BinaryNatCode.encode]
    rfl

end LeanCanny.Algebra.FixedWidthCoordinatePowerBits
