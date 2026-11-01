/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPolynomialLayout
public import LeanCanny.Algebra.MacaulayEntryEncoding
public import LeanCanny.Computation.PolyTimeBinaryRange

/-! # Native monomial matches for a binary power

Only the number and widths of spatial exponent blocks are unary. The
power and selected coordinate remain binary. Literal exponent words are
compared coordinate by coordinate, including short or redundant words.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthPowerMonomial
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial

def Matches (A W D selected : List Bool → ℕ) (target : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i < A q, FixedWidthQuery.coordinate W target q i = if i = selected q then D q else 0

instance (A W D selected : List Bool → ℕ) (target : List Bool → List Bool) (q : List Bool) :
    Decidable (Matches A W D selected target q) := inferInstanceAs (Decidable (∀ i < _, _))

theorem matches_FP (A W D selected : List Bool → ℕ) (target : List Bool → List Bool)
    (hA : UnaryFn A) (hW : UnaryFn W) (hD : BinaryFn D) (hs : BinaryFn selected) (ht : target ∈ FP) :
    FPPred (Matches A W D selected target) := by
  have HR : BinaryFn (fun p => Nat.fromBitsLE
      (FixedWidthQuery.read A W target (MacaulayBits.loopQuery p))) :=
    BinaryFn.fromBits (mem_FP_comp MacaulayBits.loopQuery_mem_FP (FixedWidthQuery.read_mem_FP hA hW ht))
  have HI : BinaryFn (fun p => (pairSnd p).length) := BinaryFn.ofUnary UnaryFn.index
  have HS : BinaryFn (fun p => selected (pairFst p)) := hs.comp pairFst_mem_FP
  have HD : BinaryFn (fun p => D (pairFst p)) := hD.comp pairFst_mem_FP
  have HE := BinaryFn.ite (HI.eq HS) HD (BinaryFn.const 0)
  apply ((HR.eq HE).forall_lt hA).of_iff
  intro q
  simp only [Matches, MacaulayBits.loopQuery, pairFst_pair, pairSnd_pair, List.length_replicate]
  have HREAD (i : ℕ) (hi : i < A q) : Nat.fromBitsLE
      (FixedWidthQuery.read A W target (pair q (BinaryNatCode.encode i))) =
      FixedWidthQuery.coordinate W target q i := by
    rw [FixedWidthQuery.read_packet]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, FixedWidthQuery.entry, hi, ite_true]
  constructor
  · intro h i hi
    exact (HREAD i hi) ▸ h i hi
  · intro h i hi
    exact (HREAD i hi).symm ▸ h i hi

theorem native_coordinate (A W : List Bool → ℕ) (target : List Bool → List Bool) (q : List Bool) (i : Fin (A q)) :
    nativeExponent (Equiv.refl (Fin (A q))) (W q) (Nat.fromBitsLE (target q)) i =
      FixedWidthQuery.coordinate W target q i.val := by
  simp only [nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply]
  rw [entry_eq_digit, ← drop_value, ← BinaryNat.value_take]
  rfl

theorem matches_iff (A W D selected : List Bool → ℕ) (target : List Bool → List Bool)
    (q : List Bool) (hs : selected q < A q) :
    Matches A W D selected target q ↔
      nativeExponent (Equiv.refl (Fin (A q))) (W q) (Nat.fromBitsLE (target q)) =
        Finsupp.single ⟨selected q, hs⟩ (D q) := by
  rw [Finsupp.ext_iff]
  simp only [native_coordinate, Finsupp.single_apply, Fin.ext_iff]
  constructor
  · intro h i
    simpa only [eq_comm] using h i.val i.isLt
  · intro h i hi
    simpa only [eq_comm] using h ⟨i, hi⟩

def multiplicity (A W D : List Bool → ℕ) (target : List Bool → List Bool) (q : List Bool) : ℕ :=
  ∑ i ∈ Finset.range (A q), if Matches A W D (fun _ => i) target q then 1 else 0

theorem multiplicity_binary (A W D : List Bool → ℕ) (target : List Bool → List Bool)
    (hA : UnaryFn A) (hW : UnaryFn W) (hD : BinaryFn D) (ht : target ∈ FP) :
    BinaryFn (multiplicity A W D target) := by
  have HM := matches_FP (A ∘ pairFst) (W ∘ pairFst) (D ∘ pairFst) (fun p => (pairSnd p).length)
    (target ∘ pairFst) (hA.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP)
    (hD.comp pairFst_mem_FP) (BinaryFn.ofUnary UnaryFn.index) (mem_FP_comp pairFst_mem_FP ht)
  exact (BinaryFn.sum hA (BinaryFn.ite HM (BinaryFn.const 1) (BinaryFn.const 0))).of_eq (fun q => by
    simp only [multiplicity, Matches, FixedWidthQuery.coordinate, Function.comp_apply, pairFst_pair,
      pairSnd_pair, List.length_replicate]
    rfl)

theorem multiplicity_eq (A W D : List Bool → ℕ) (target : List Bool → List Bool) (q : List Bool) :
    multiplicity A W D target q = ∑ i : Fin (A q), if Finsupp.single i (D q) =
      nativeExponent (Equiv.refl (Fin (A q))) (W q) (Nat.fromBitsLE (target q)) then 1 else 0 := by
  rw [multiplicity, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [matches_iff A W D (fun _ => i.val) target q i.isLt, eq_comm]

end LeanCanny.Algebra.FixedWidthPowerMonomial
