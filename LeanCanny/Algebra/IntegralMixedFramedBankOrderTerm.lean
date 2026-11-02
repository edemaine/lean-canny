/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankTermReaders
public import LeanCanny.ETR.EncodingFP
/-! # Native bounded syntax for comparing two retained bank coordinates

Binary retained labels are bounded before unary variable serialization.
The actual label guard is preserved separately; clipping does not turn an
invalid retained label into a valid comparison.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankOrderBits
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)

noncomputable def count (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (c : List Bool) := (atKey P D H (key c)).count
theorem count_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (hk : key∈FP) : UnaryFn (count P D H key) :=
  (IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp hk

noncomputable def clipped (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (index : List Bool→ℕ) (c : List Bool) := min (index c) (count P D H key c-1)
theorem clipped_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (hk : key∈FP) (index : List Bool→ℕ) (hi : BinaryFn index) :
    UnaryFn (clipped P D H key index) :=
  (UnaryFn.fromBitsLE_min hi.bits_mem_FP ((count_unary P a D H key hk).sub (UnaryFn.const 1))).of_eq
    (fun c=>by rw [BinaryNatCode.encode,Nat.fromBitsLE_bits]; rfl)

noncomputable def chronological (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (index : List Bool→ℕ) (c : List Bool) := count P D H key c-1-clipped P D H key index c
theorem chronological_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (hk : key∈FP) (index : List Bool→ℕ) (hi : BinaryFn index) :
    UnaryFn (chronological P D H key index) :=
  ((count_unary P a D H key hk).sub (UnaryFn.const 1)).sub (clipped_unary P a D H key hk index hi)

noncomputable def term (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (left right : List Bool→ℕ) (c : List Bool) : Term :=
  .add (.var (chronological P D H key left c)) (.mul (.const (-1)) (.var (chronological P D H key right c)))
noncomputable def word (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (left right : List Bool→ℕ) (c : List Bool) := (term P D H key left right c).toData.toBits

theorem word_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (hk : key∈FP) (left right : List Bool→ℕ) (hl : BinaryFn left) (hr : BinaryFn right) :
    word P D H key left right∈FP := by
  have HL := Term.variableBits_mem_FP (chronological_unary P a D H key hk left hl)
  have HR := Term.variableBits_mem_FP (chronological_unary P a D H key hk right hr)
  exact mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 HL
    (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (Term.const (-1)).toData.toBits) HR))
    (fun c=>by simp only [word,term,Term.add_toBits,Term.mul_toBits,Term.variableBits_eq])

def Labels (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (left right : List Bool→ℕ) (c : List Bool) : Prop :=
  left c<count P D H key c ∧ right c<count P D H key c
theorem labels_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (hk : key∈FP) (left right : List Bool→ℕ) (hl : BinaryFn left) (hr : BinaryFn right) :
    FPPred (Labels P D H key left right) :=
  (hl.lt (BinaryFn.ofUnary (count_unary P a D H key hk))).and
    (hr.lt (BinaryFn.ofUnary (count_unary P a D H key hk)))

theorem chronological_lt (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (index : List Bool→ℕ) (c : List Bool) (hc : 0<count P D H key c) :
    chronological P D H key index c<count P D H key c := by unfold chronological; omega
theorem chronological_reverse (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (index : List Bool→ℕ) (c : List Bool) (hi : index c<count P D H key c) :
    IntegralMixedFramedBankTermBits.reverseIndex P D H (key c) (chronological P D H key index c)=index c := by
  unfold IntegralMixedFramedBankTermBits.reverseIndex chronological clipped count
  change index c<(atKey P D H (key c)).count at hi
  omega

end LeanCanny.Algebra.IntegralMixedFramedBankOrderBits
