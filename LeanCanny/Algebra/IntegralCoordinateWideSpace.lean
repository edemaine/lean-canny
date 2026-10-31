/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCoordinateCoefficientSpace
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Canonical coefficient queries with independent exponent widths

The query width need not equal the bounded monomial-basis digit width.
An FP guard rejects coordinates outside the basis box before repacking;
the accepted query still reads the original multiplication matrix at
column zero. The exponential basis radix stays binary throughout.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCoordinateCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def Fits (F : Family) (V : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) : Prop :=
  ∀ i < F.arity c, FixedWidthQuery.entry F.arity V target c i < 2 ^ F.width c

instance (F : Family) (V : List Bool → ℕ) (target : List Bool → List Bool) :
    DecidablePred (Fits F V target) := fun c =>
  inferInstanceAs (Decidable (∀ i < F.arity c, FixedWidthQuery.entry F.arity V target c i < 2 ^ F.width c))

theorem fits_FP (F : Family) (V : List Bool → ℕ) (target : List Bool → List Bool)
    (hA : UnaryFn F.arity) (hB : UnaryFn F.width) (hV : UnaryFn V) (ht : target ∈ FP) :
    FPPred (Fits F V target) := by
  have HR : FixedWidthQuery.read F.arity V target ∈ FP := FixedWidthQuery.read_mem_FP hA hV ht
  have HE : (fun c => pair (pairFst c) (BinaryNatCode.encode (pairSnd c).length)) ∈ FP :=
    mem_FP_pair pairFst_mem_FP (bits_mem_FP UnaryFn.index)
  have HB : BinaryFn (fun c => 2 ^ F.width (pairFst c)) := (BinaryFn.const 2).powUnary hB.lift
  have HG := (BinaryFn.fromBits (mem_FP_comp HE HR)).lt HB
  apply (HG.forall_lt hA).of_iff
  intro c
  simp only [Fits, Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]
  have HP (i : ℕ) : Nat.fromBitsLE (FixedWidthQuery.read F.arity V target (pair c i.bits)) =
      FixedWidthQuery.entry F.arity V target c i := by
    change Nat.fromBitsLE (FixedWidthQuery.read F.arity V target (pair c (BinaryNatCode.encode i))) = _
    rw [FixedWidthQuery.read_packet]
    exact Nat.fromBitsLE_bits _
  exact forall₂_congr (fun i _ => Iff.of_eq (congrArg (fun x => x < 2 ^ F.width c) (HP i)))

theorem wide_exponent_coordinate (F : Family) (V : List Bool → ℕ) (target : List Bool → List Bool)
    (c : List Bool) (i : Fin (F.arity c)) :
    nativeExponent (Equiv.refl _) (V c) (Nat.fromBitsLE (target c)) i =
      FixedWidthQuery.entry F.arity V target c i.val := by
  simp only [nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply,
    FixedWidthBlockRenameBits.entry_bits, FixedWidthQuery.entry, i.isLt, ite_true, FixedWidthQuery.coordinate]

theorem wide_coefficient (F : Family) (V : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) :
    (F.polynomial c).coeff (nativeExponent (Equiv.refl _) (V c) (Nat.fromBitsLE (target c))) =
      if Fits F V target c then (F.polynomial c).coeff (nativeExponent (Equiv.refl _) (F.width c)
        (Nat.fromBitsLE (FixedWidthQuery.repack F.arity V F.arity F.width target c))) else 0 := by
  by_cases hf : Fits F V target c
  · rw [ite_eq_left hf]
    congr 1
    ext i
    rw [wide_exponent_coordinate F V target c i,
      wide_exponent_coordinate F F.width (FixedWidthQuery.repack F.arity V F.arity F.width target) c i]
    simp only [FixedWidthQuery.entry, i.isLt, ite_true]
    simpa only [FixedWidthQuery.entry, i.isLt, ite_true] using
      (FixedWidthQuery.coordinate_repack F.arity V F.arity F.width target c i.val i.isLt (hf i.val i.isLt)).symm
  · rw [ite_eq_right hf]
    obtain ⟨i, hi⟩ := not_forall.mp hf
    obtain ⟨hi, he⟩ := not_imp.mp hi
    let := F.ring c
    by_contra hn
    have HS := MvPolynomial.mem_support_iff.mpr hn
    have HB := (F.basis c).representative_support (F.element c) _ HS (⟨i, hi⟩ : Fin (F.arity c))
    rw [wide_exponent_coordinate F V target c ⟨i, hi⟩] at HB
    exact he HB

theorem wide_evaluator (F : Family) (V : List Bool → ℕ) (target modulus entry : List Bool → List Bool)
    (hA : UnaryFn F.arity) (hB : UnaryFn F.width) (hV : UnaryFn V)
    (ht : target ∈ FP) (hm : modulus ∈ FP) (E : SpaceFunction entry)
    (he : ∀ c mw (i j : Fin (count (F.arity c) (F.width c))),
      entry (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
        residueBits ((F.matrix c i j : ℤ) : ZMod (Nat.fromBitsLE mw + 1))) :
    SpaceFunction (FixedWidthRowBits.value F.arity V F.polynomial target modulus) := by
  have HR := evaluator F (FixedWidthQuery.repack F.arity V F.arity F.width target) modulus entry
    hA hB (FixedWidthQuery.repack_mem_FP hA hV hA hB ht) hm E he
  have HG := SpaceFunction.branch (fun c => decide (Fits F V target c))
    (fits_FP F V target hA hB hV ht).flag_mem_FP HR (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine HG.congr (funext fun c => ?_)
  simp only [FixedWidthRowBits.value]
  rw [wide_coefficient F V target c]
  by_cases hf : Fits F V target c
  · simp only [hf, decide_eq_true_eq, ite_true]
  · simp only [hf, decide_eq_true_eq, ite_false, Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode]
    rfl

end LeanCanny.Algebra.IntegralCoordinateCoefficientBits
