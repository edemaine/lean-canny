/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankCoordinateBounds
/-! # A literal bank snapshot normalizes original coefficient packets

The count and denominator vector are the actual source-framed retained bank.
Packing them together permits ordinary equality under full saved-key
readback; no dependent index or interpreted-bank oracle is supplied.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankSnapshotBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical BigOperators

structure Snapshot where
  count : ℕ
  denominator : Fin count → ℤ

noncomputable def atKey (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) : Snapshot :=
  ⟨(IntegralMixedFramedHistoryFamilyBits.family P D H).birth key,
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).bank.denominator⟩

noncomputable def Snapshot.common (s : Snapshot) : ℤ := ∏ i,s.denominator i
noncomputable def Snapshot.cofactor (s : Snapshot) (i : ℕ) : ℤ := ∏ j : Fin s.count,if j.val=i then 1 else s.denominator j
noncomputable def Snapshot.coordinateDenominator (s : Snapshot) (i : ℕ) : ℤ :=
  if hi : i<s.count then s.denominator ⟨i,hi⟩ else 0

def packet (key modulusWord : List Bool) (i k : ℕ) : List Bool :=
  pair (pair key modulusWord) (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))

theorem packet_base (key mw : List Bool) (i k : ℕ) : PaddedIntegralGeneratorSource.base (packet key mw i k)=key := by
  simp only [packet,PaddedIntegralGeneratorSource.base,pairFst_pair]

theorem packet_snapshot (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key mw : List Bool) (i k : ℕ) : atKey P D H (PaddedIntegralGeneratorSource.base (packet key mw i k))=atKey P D H key :=
  congrArg (atKey P D H) (packet_base key mw i k)

theorem count_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    UnaryFn (fun key => (atKey P D H key).count) :=
  (IntegralMixedFullHistoryFamilyBits.prefix_unary P a).of_eq
    (fun key => (IntegralMixedFramedHistoryFamilyBits.family_birth P D H key).symm)

theorem cofactor_at (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (skip : List Bool → ℕ) (q : List Bool) : IntegralMixedFramedBankProductBits.integer P D H skip q=
      (atKey P D H (PaddedIntegralGeneratorSource.base q)).cofactor (skip q) :=
  IntegralMixedFramedBankProductBits.integer_fin P D H skip q

theorem cofactor_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key mw : List Bool) (i k : ℕ) :
    IntegralMixedFramedBankProductBits.integer P D H IntegralMixedFramedBankDenominatorBits.index (packet key mw i k)=
      (atKey P D H key).cofactor i := by
  rw [cofactor_at,packet_snapshot]
  simp only [IntegralMixedFramedBankDenominatorBits.index,packet,PaddedIntegralGeneratorSource.row,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem common_at (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedHistory.commonDenominator (IntegralMixedFramedBankDenominatorBits.state P D H q)=
      (atKey P D H (PaddedIntegralGeneratorSource.base q)).common := rfl

end LeanCanny.Algebra.IntegralMixedFramedBankSnapshotBits
