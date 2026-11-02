/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryLimitRecordSemantics
public import LeanCanny.Algebra.IntegralMixedFramedHistoryScript
/-! # Bounded auxiliary labels decode to the exact original limit-cut command -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryLimitRecord
open LeanCanny.Algebra IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem written_degree {n : ℕ} (S : SpatialSource (n+2)) (k m0 c d : ℕ)
    (hd : d≤IntegralMixedExceptionalBounds.auxiliaryCap (n+3) S.degree) :
    IntegralMixedCanonicalUnitRuleBits.writtenDegree S (record n k m0 c d)=d := by
  unfold IntegralMixedCanonicalUnitRuleBits.writtenDegree
  rw [record_field]
  simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]
  exact Nat.mod_eq_of_lt (by simpa only [Nat.add_assoc] using Nat.lt_succ_of_le hd)

theorem limit_kind {n : ℕ} (S : SpatialSource (n+2)) (k m0 c d : ℕ)
    (hc : c<IntegralMixedLimitCoordinate.ChoiceBound S
      (IntegralMixedCanonicalUnitRuleBits.virtual (n+2) (by omega) (m0+k) (record n k m0 c d))) :
    IntegralMixedCanonicalUnitRuleBits.kind S (by omega) (m0+k) (record n k m0 c d) =
      .limitCoordinate ⟨0,Nat.succ_pos _⟩ ⟨c,hc⟩ := by
  unfold IntegralMixedCanonicalUnitRuleBits.kind
  congr 1
  · apply Fin.ext
    change Nat.fromBitsLE (IntegralMixedUnitRecordCode.field (record n k m0 c d) 4) %
      ((n+2)-IntegralMixedUnitRecordCode.virtualOffset (n+2) (record n k m0 c d)+1) = 0
    rw [record_field]
    simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
    exact Nat.zero_mod _
  · apply Fin.ext
    change Nat.fromBitsLE (IntegralMixedUnitRecordCode.field (record n k m0 c d) 8) %
      IntegralMixedLimitCoordinate.ChoiceBound S
        (IntegralMixedCanonicalUnitRuleBits.virtual (n+2) (by omega) (m0+k) (record n k m0 c d)) = c
    rw [record_field]
    simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
      BinaryNatCode.encode,Nat.fromBitsLE_bits]
    exact Nat.mod_eq_of_lt hc

theorem cut_command {n B : ℕ} (S : SpatialSource (n+2)) (k m0 c d : ℕ)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) S.degree≤2^B)
    (hc : c<IntegralMixedLimitCoordinate.ChoiceBound S
      (IntegralMixedCanonicalUnitRuleBits.virtual (n+2) (by omega) (m0+k) (record n k m0 c d)))
    (hd : d≤IntegralMixedExceptionalBounds.auxiliaryCap (n+3) S.degree) :
    IntegralMixedCanonicalUnitRuleBits.command S (by omega) (m0+k) (record n k m0 c d) hcap =
      .cut (IntegralMixedCanonicalUnitRuleBits.virtual (n+2) (by omega) (m0+k) (record n k m0 c d))
        (.limitCoordinate ⟨0,Nat.succ_pos _⟩ ⟨c,hc⟩) d hd (hd.trans hcap) := by
  unfold IntegralMixedCanonicalUnitRuleBits.command
  rw [critical_record]
  simp only [Bool.false_eq_true,ite_false]
  congr 1
  · exact limit_kind S k m0 c d hc
  · exact written_degree S k m0 c d hd

/-- The original instruction keeps its once-augmented source literally unchanged. -/
noncomputable def instruction {n B : ℕ} (S : SpatialSource (n+2)) (k m0 c d : ℕ)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) S.degree≤2^B) :
    IntegralMixedFramedHistoryScript.Instruction (n+2) B where
  source := S
  source_cap := (by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K; omega :
    PurePowerReductionBounds.dimension (n+3) S.degree ≤ IntegralMixedExceptionalBounds.auxiliaryCap (n+3) S.degree).trans hcap
  command := IntegralMixedCanonicalUnitRuleBits.command S (by omega) (m0+k) (record n k m0 c d) hcap

theorem instruction_source {n B : ℕ} (S : SpatialSource (n+2)) (k m0 c d : ℕ)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) S.degree≤2^B) :
    (instruction S k m0 c d hcap).source=S := rfl
end LeanCanny.Encoding.IntegralMixedAuxiliaryLimitRecord
