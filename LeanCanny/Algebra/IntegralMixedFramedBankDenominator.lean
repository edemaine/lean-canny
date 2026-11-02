/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedLeadingSpace
/-! # Actual retained integer denominator residues from original syntax

Each retained label is read from its chronological creating producer, with
the original modulus word preserved. Invalid retained labels return zero.
The construction covers terminal padded prefixes as well as active births.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankDenominatorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan prefixLength)
open IntegralMixedFramedCompanionQueryBits (root sourceBirth callerModulus)
open scoped Classical

noncomputable abbrev family (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :=
  IntegralMixedFramedHistoryFamilyBits.family P D H
noncomputable abbrev state (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  (family P D H).state (PaddedIntegralGeneratorSource.base q)
noncomputable def count (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  (family P D H).birth (PaddedIntegralGeneratorSource.base q)
theorem count_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    count P D H q=sourceBirth P q := IntegralMixedFramedHistoryFamilyBits.family_birth P D H _
theorem count_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    UnaryFn (count P D H) :=
  (IntegralMixedFramedCompanionQueryBits.sourceBirth_unary P a).of_eq (fun q => (count_eq P D H q).symm)

def index (q : List Bool) := Nat.fromBitsLE (PaddedIntegralGeneratorSource.row q)
theorem index_binary : BinaryFn index := BinaryFn.fromBits PaddedIntegralGeneratorSource.row_FP

noncomputable def integerAt (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (i : ℕ) : ℤ :=
  if hi : i<count P D H q then (state P D H q).bank.denominator ⟨i,hi⟩ else 0

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  residueBits (integerAt P D H q (index q) : ZMod (callerModulus q))

noncomputable def creatorBirth (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  count P D H q-1-index q
noncomputable def creatorKey (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  IntegralMixedFramedHistoryFamilyBits.keyAt (root q) (creatorBirth P D H q) []
noncomputable def creatorPacket (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  pair (pair (creatorKey P D H q) (PaddedIntegralGeneratorSource.modulus q)) []

theorem creatorPacket_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    creatorPacket P D H∈FP := by
  have HB : BinaryFn (creatorBirth P D H) :=
    ((BinaryFn.ofUnary (count_unary P a D H)).sub (BinaryFn.const 1)).sub index_binary
  have HK : creatorKey P D H∈FP := mem_FP_pair IntegralMixedFramedCompanionQueryBits.root_FP
    (mem_FP_pair HB.bits_mem_FP (constFn_mem_FP []))
  exact mem_FP_pair (mem_FP_pair HK PaddedIntegralGeneratorSource.modulus_FP) (constFn_mem_FP [])

theorem creator_leading (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hi : index q<count P D H q) :
    IntegralMixedFramedCompanionBits.leading P D H (creatorKey P D H q)=integerAt P D H q (index q) := by
  rw [integerAt,dite_eq_left hi]
  have HH := IntegralMixedFramedHistoryFamilyBits.retained_leading_key P D H
    (PaddedIntegralGeneratorSource.base q) ⟨index q,hi⟩ []
  unfold creatorKey creatorBirth
  rw [count_eq]
  exact HH.symm

theorem creator_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hi : index q<count P D H q) :
    IntegralMixedFramedLeadingBits.value P D H (creatorPacket P D H q)=value P D H q := by
  have HM : callerModulus (creatorPacket P D H q)=callerModulus q := by
    simp only [callerModulus,creatorPacket,PaddedIntegralGeneratorSource.modulus,pairFst_pair,pairSnd_pair]
  unfold IntegralMixedFramedLeadingBits.value value
  rw [HM]
  simp only [creatorPacket,PaddedIntegralGeneratorSource.base,pairFst_pair]
  rw [creator_leading P D H q hi]

noncomputable def finish (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) :=
  if index (pairFst z)<count P D H (pairFst z) then pairSnd z else []
theorem finish_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    finish P D H∈FP := by
  have HG : FPPred (fun q => index q<count P D H q) := index_binary.lt (BinaryFn.ofUnary (count_unary P a D H))
  exact (HG.comp pairFst_mem_FP).ite_mem_FP pairSnd_mem_FP (constFn_mem_FP [])

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root) : SpaceFunction (value P D H) := by
  have EL := IntegralMixedFramedLeadingBits.evaluator P a D H s hs hF hL
  have EE := EL.call (creatorPacket P D H) (finish P D H) (creatorPacket_FP P a D H) (finish_FP P a D H)
  exact EE.congr (funext fun q => by
    simp only [finish,pairFst_pair,pairSnd_pair]
    split_ifs with hi
    · exact creator_value P D H q hi
    · unfold value integerAt
      rw [dite_eq_right hi]
      exact ArithmeticBits.zero_residueBits _)

end LeanCanny.Algebra.IntegralMixedFramedBankDenominatorBits
