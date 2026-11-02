/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedUnitSnapshot
public import LeanCanny.Algebra.MatrixPowerArithmeticFP
/-! # Native scalar cells derived from literal saved-birth unit selectors -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedUnitCellsBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedUnitSnapshotBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def packet (P : Parameters) (q : List Bool) := pair (IntegralMixedVirtualTaskBits.saved P q) (BinaryNatCode.encode (get P .slot8 q))
attribute [local irreducible] packet IntegralMixedVirtualTaskBits.saved IntegralCriticalHistoryTask.get IntegralMixedFramedUnitBodyBits.reference reference

theorem packet_FP (P : Parameters) (a : Access P) : packet P ∈ FP := by
  unfold packet
  exact mem_FP_pair (IntegralMixedVirtualTaskBits.saved_FP P a) (get_binary P a .slot8).bits_mem_FP

theorem active_pred (P : Parameters) (a : Access P) (writer : List Bool → List Bool) (hw : writer ∈ FP) :
    FPPred (active P writer) := by
  have HT : FPPred (fun q => IntegralMixedFramedUnitBodyBits.active writer true (IntegralMixedVirtualTaskBits.saved P q) (get P .slot8 q) = true) := by
    have H := (FPPred.of_flag (IntegralMixedFramedUnitBodyBits.active_FP writer hw true)).comp (packet_FP P a)
    simpa only [packet, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using H
  have HF : FPPred (fun q => IntegralMixedFramedUnitBodyBits.active writer false (IntegralMixedVirtualTaskBits.saved P q) (get P .slot8 q) = true) := by
    have H := (FPPred.of_flag (IntegralMixedFramedUnitBodyBits.active_FP writer hw false)).comp (packet_FP P a)
    simpa only [packet, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using H
  have HC := (get_binary P a .slot15).eq (BinaryFn.const 1)
  have HN : FPPred (fun q => get P .slot8 q < P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1) :=
    (get_binary P a .slot8).lt (BinaryFn.ofUnary (((a.ambient.comp pairFst_mem_FP).comp (IntegralMixedVirtualTaskBits.saved_FP P a)).add (UnaryFn.const 1)))
  apply (HN.and ((HC.and HT).or (HC.not.and HF))).of_iff
  intro q
  unfold active physical
  rw [IntegralMixedHeightCellsBits.context_saved]
  by_cases hc : get P .slot15 q = 1 <;> simp only [hc, decide_true, decide_false, true_and, false_and, or_false, false_or, not_true_eq_false, not_false_eq_true]

theorem reference_binary (P : Parameters) (a : Access P) (writer : List Bool → List Bool) (hw : writer ∈ FP) :
    BinaryFn (reference P writer) := by
  have HT : BinaryFn (fun q => IntegralMixedFramedUnitBodyBits.reference writer true (IntegralMixedVirtualTaskBits.saved P q) (get P .slot8 q)) := by
    have H : BinaryFn (fun q => IntegralMixedFramedUnitBodyBits.reference writer true (pairFst (packet P q)) (Nat.fromBitsLE (pairSnd (packet P q)))) := (IntegralMixedFramedUnitBodyBits.reference_binary writer hw true).comp (packet_FP P a)
    simpa only [packet, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using H
  have HF : BinaryFn (fun q => IntegralMixedFramedUnitBodyBits.reference writer false (IntegralMixedVirtualTaskBits.saved P q) (get P .slot8 q)) := by
    have H : BinaryFn (fun q => IntegralMixedFramedUnitBodyBits.reference writer false (pairFst (packet P q)) (Nat.fromBitsLE (pairSnd (packet P q)))) := (IntegralMixedFramedUnitBodyBits.reference_binary writer hw false).comp (packet_FP P a)
    simpa only [packet, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using H
  apply BinaryFn.of_bits (mem_FP_of_eq (BinaryFn.ite ((get_binary P a .slot15).eq (BinaryFn.const 1)) HT HF).bits_mem_FP ?_)
  intro q
  unfold reference physical
  rw [IntegralMixedHeightCellsBits.context_saved]
  by_cases hc : get P .slot15 q = 1 <;> simp only [hc, decide_true, decide_false, ite_true, ite_false]

noncomputable def flag (P : Parameters) (writer : List Bool → List Bool) (z : List Bool) : Prop :=
  let q := pairFst z
  let tag := Nat.fromBitsLE (pairFst (pairSnd z))
  let i := Nat.fromBitsLE (pairSnd (pairSnd z))
  (tag = 1 ∧ active P writer q ∧ reference P writer q = i) ∨ tag = 2 ∨
    (tag = 3 ∧ get P .slot8 q = IntegralMixedFramedUnitBodyBits.height P writer (IntegralMixedVirtualTaskBits.saved P q))

theorem flag_pred (P : Parameters) (a : Access P) (writer : List Bool → List Bool) (hw : writer ∈ FP) : FPPred (flag P writer) := by
  have HT : BinaryFn (fun z => Nat.fromBitsLE (pairFst (pairSnd z))) := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have HI : BinaryFn (fun z => Nat.fromBitsLE (pairSnd (pairSnd z))) := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have HR : BinaryFn (fun z => reference P writer (pairFst z)) := Turing.MultiTapeTM.ComputableTidilyInPolyTime.comp (f := reference P writer) (g := pairFst) (reference_binary P a writer hw) pairFst_mem_FP
  have HG : BinaryFn (fun z => get P .slot8 (pairFst z)) := (get_binary P a .slot8).comp pairFst_mem_FP
  have HH0 : BinaryFn (fun q => IntegralMixedFramedUnitBodyBits.height P writer (IntegralMixedVirtualTaskBits.saved P q)) :=
    (IntegralMixedFramedUnitBodyBits.height_binary P a writer hw).comp (IntegralMixedVirtualTaskBits.saved_FP P a)
  have HH : BinaryFn (fun z => IntegralMixedFramedUnitBodyBits.height P writer (IntegralMixedVirtualTaskBits.saved P (pairFst z))) := HH0.comp pairFst_mem_FP
  exact (((HT.eq (BinaryFn.const 1)).and (((active_pred P a writer hw).comp pairFst_mem_FP).and
    (HR.eq HI))).or
    ((HT.eq (BinaryFn.const 2)).or ((HT.eq (BinaryFn.const 3)).and
      (HG.eq HH))))

theorem cell_flag (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (h : Snapshot P D H writer) (z : List Bool) :
    IntegralMixedFramedScalarCellsBits.cell P D H (pairFst z)
      (Nat.fromBitsLE (pairFst (pairSnd z))) (Nat.fromBitsLE (pairSnd (pairSnd z))) = if flag P writer z then 1 else 0 := by
  rw [cell_eq P D H writer h]
  unfold flag
  by_cases h1 : Nat.fromBitsLE (pairFst (pairSnd z)) = 1
  · simp only [h1, ite_true, true_and, show (1 : ℕ) ≠ 2 by decide, show (1 : ℕ) ≠ 3 by decide, false_and, or_false]
  · by_cases h2 : Nat.fromBitsLE (pairFst (pairSnd z)) = 2
    · simp only [h2, show (2 : ℕ) ≠ 1 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true, false_and, false_or, true_or]
    · by_cases h3 : Nat.fromBitsLE (pairFst (pairSnd z)) = 3
      · simp only [h3, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ite_false, ite_true, false_and, false_or, true_and]
      · simp only [h1, h2, h3, ite_false, false_and, false_or]

attribute [local irreducible] modulus

theorem reader_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (hw : writer ∈ FP) (h : Snapshot P D H writer) :
    IntegralMixedFramedScalarCellsBits.reader P D H ∈ FP := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  have HO := mem_FP_comp HM.bits_mem_FP ArithmeticBits.one_mem_FP
  apply mem_FP_of_eq ((flag_pred P a writer hw).ite_mem_FP HO (constFn_mem_FP []))
  intro z
  unfold IntegralMixedFramedScalarCellsBits.reader
  rw [cell_flag P D H writer h]
  by_cases hf : flag P writer z
  · rw [ite_eq_left hf, ite_eq_left hf]
    simpa only [Function.comp_apply, Int.cast_one] using ArithmeticBits.one_residueBits (modulus P (pairFst z))
  · rw [ite_eq_right hf, ite_eq_right hf]
    simpa only [ArithmeticBits.zero, Int.cast_zero] using ArithmeticBits.zero_residueBits (modulus P (pairFst z))

theorem primitive (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (hw : writer ∈ FP) (h : Snapshot P D H writer) :
    IntegralMixedFramedScalarCellsBits.Primitive P D H :=
  SpaceFunction.ofFP _ (reader_FP P a D H writer hw h)

theorem leading_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (h : Snapshot P D H writer) : IntegralMixedFramedScalarCellsBits.leadingValue P D ∈ FP := by
  apply mem_FP_of_eq (mem_FP_comp (modulus_binary P a).bits_mem_FP ArithmeticBits.one_mem_FP)
  intro q
  unfold IntegralMixedFramedScalarCellsBits.leadingValue
  rw [leading_one P D H writer h]
  simpa only [Function.comp_apply, Int.cast_one] using ArithmeticBits.one_residueBits (modulus P q)
end LeanCanny.Algebra.IntegralMixedFramedUnitCellsBits
