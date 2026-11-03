/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCoordinateWideSpace
/-! # Independent exponent widths for any original polynomial in a fixed box

The source need not be an algebra representative. A native fit guard rejects
exponents outside the proved source box before one original coefficient call.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthBoxRepackBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def Fits (A B : List Bool → ℕ) (V : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) : Prop :=
  ∀ i < A c, FixedWidthQuery.entry A V target c i < 2 ^ B c

instance (A B : List Bool → ℕ) (V : List Bool → ℕ) (target : List Bool → List Bool) :
    DecidablePred (Fits A B V target) := fun c =>
  inferInstanceAs (Decidable (∀ i < A c, FixedWidthQuery.entry A V target c i < 2 ^ B c))

theorem fits_FP (A B : List Bool → ℕ) (V : List Bool → ℕ) (target : List Bool → List Bool)
    (hA : UnaryFn A) (hB : UnaryFn B) (hV : UnaryFn V) (ht : target ∈ FP) :
    FPPred (Fits A B V target) := by
  have HR : FixedWidthQuery.read A V target ∈ FP := FixedWidthQuery.read_mem_FP hA hV ht
  have HE : (fun c => pair (pairFst c) (BinaryNatCode.encode (pairSnd c).length)) ∈ FP :=
    mem_FP_pair pairFst_mem_FP (bits_mem_FP UnaryFn.index)
  have HB : BinaryFn (fun c => 2 ^ B (pairFst c)) := (BinaryFn.const 2).powUnary hB.lift
  have HG := (BinaryFn.fromBits (mem_FP_comp HE HR)).lt HB
  apply (HG.forall_lt hA).of_iff
  intro c
  simp only [Fits, Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]
  have HP (i : ℕ) : Nat.fromBitsLE (FixedWidthQuery.read A V target (pair c i.bits)) =
      FixedWidthQuery.entry A V target c i := by
    change Nat.fromBitsLE (FixedWidthQuery.read A V target (pair c (BinaryNatCode.encode i))) = _
    rw [FixedWidthQuery.read_packet]
    exact Nat.fromBitsLE_bits _
  exact forall₂_congr (fun i _ => Iff.of_eq (congrArg (fun x => x < 2 ^ B c) (HP i)))

theorem wide_exponent_coordinate (A _B : List Bool → ℕ) (V : List Bool → ℕ) (target : List Bool → List Bool)
    (c : List Bool) (i : Fin (A c)) :
    nativeExponent (Equiv.refl _) (V c) (Nat.fromBitsLE (target c)) i =
      FixedWidthQuery.entry A V target c i.val := by
  simp only [nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply,
    FixedWidthBlockRenameBits.entry_bits, FixedWidthQuery.entry, i.isLt, ite_true, FixedWidthQuery.coordinate]

theorem wide_coefficient (A B : List Bool → ℕ)
    (p : (c : List Bool)→MvPolynomial (Fin (A c)) ℤ)
    (hp : ∀c e,e∈(p c).support→∀i,e i<2^B c) (V : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) :
    (p c).coeff (nativeExponent (Equiv.refl _) (V c) (Nat.fromBitsLE (target c))) =
      if Fits A B V target c then (p c).coeff (nativeExponent (Equiv.refl _) (B c)
        (Nat.fromBitsLE (FixedWidthQuery.repack A V A B target c))) else 0 := by
  by_cases hf : Fits A B V target c
  · rw [ite_eq_left hf]
    congr 1
    ext i
    rw [wide_exponent_coordinate A B V target c i,
      wide_exponent_coordinate A B B (FixedWidthQuery.repack A V A B target) c i]
    simp only [FixedWidthQuery.entry, i.isLt, ite_true]
    simpa only [FixedWidthQuery.entry, i.isLt, ite_true] using
      (FixedWidthQuery.coordinate_repack A V A B target c i.val i.isLt (hf i.val i.isLt)).symm
  · rw [ite_eq_right hf]
    obtain ⟨i, hi⟩ := not_forall.mp hf
    obtain ⟨hi, he⟩ := not_imp.mp hi
    by_contra hn
    have HS := MvPolynomial.mem_support_iff.mpr hn
    have HB := hp c _ HS (⟨i,hi⟩ : Fin (A c))
    rw [wide_exponent_coordinate A B V target c ⟨i, hi⟩] at HB
    exact he HB

theorem evaluator (A B V : List Bool→ℕ) (p : (c : List Bool)→MvPolynomial (Fin (A c)) ℤ)
    (hp : ∀c e,e∈(p c).support→∀i,e i<2^B c) (target modulus : List Bool→List Bool)
    (hA : UnaryFn A) (hB : UnaryFn B) (hV : UnaryFn V) (ht : target∈FP)
    (E : SpaceFunction (FixedWidthRowBits.value A B p (FixedWidthQuery.repack A V A B target) modulus)) :
    SpaceFunction (FixedWidthRowBits.value A V p target modulus) := by
  have HG:=SpaceFunction.branch (fun c=>decide (Fits A B V target c))
    (fits_FP A B V target hA hB hV ht).flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine HG.congr (funext fun c=>?_)
  simp only [FixedWidthRowBits.value]
  rw [wide_coefficient A B p hp V target c]
  by_cases hf : Fits A B V target c
  · simp only [hf,decide_eq_true_eq,ite_true]
  · simp only [hf,decide_eq_true_eq,ite_false,Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode]
    rfl

end LeanCanny.Algebra.FixedWidthBoxRepackBits
