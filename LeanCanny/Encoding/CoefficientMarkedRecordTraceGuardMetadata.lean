/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceCutMetadata
/-! # The actual historical finite scan fits its original coefficient range -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTraceGuardMetadata
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedFramedHistoryFamilyBits IntegralMixedCommandHeaderBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem choice_eq (F : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRawKindBits.choice F key = kindChoice (F.kind key) := by
  cases h : F.kind key <;> simp only [IntegralMixedRawKindBits.choice, kindChoice, h]

private theorem bounds (P : IntegralCriticalHistoryTask.Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (IntegralMixedCommandHeaderBits.selection (selection P D H key)).choice ≤ 2^P.width (pairFst key) ∧
    (IntegralMixedCommandHeaderBits.selection (selection P D H key)).degree ≤ 2^P.width (pairFst key) := by
  let F := family P D H
  have hc := (IntegralMixedRawKindBits.choice_le F key).trans (F.scalar_cap key)
  have hd := (F.degree_bound key).trans (F.scalar_cap key)
  change IntegralMixedRawKindBits.choice F key ≤ 2^P.width (pairFst key) at hc
  change (IntegralMixedCommandHeaderBits.selection (selection P D H key)).degree ≤ 2^P.width (pairFst key) at hd
  refine ⟨?_, hd⟩
  change kindChoice (F.kind key) ≤ 2^P.width (pairFst key)
  rw [← choice_eq]
  exact hc

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

private theorem cap_stage (P : IntegralCriticalHistoryTask.Parameters) (ctx w : List Bool) (j : ℕ) :
    IntegralFramedTraceCutGuards.cap P (IntegralFramedTraceCutScan.stagePacket (pair ctx w) j) =
      2^P.width ctx := by
  simp only [IntegralFramedTraceCutGuards.cap, IntegralFramedTraceCutGuards.root,
    IntegralFramedTraceCutScan.stagePacket, pairFst_pair]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

/-- This includes zero/non-cut headers; the bound is not an assertion that a
specialized factor retains its declared degree. -/
theorem header_bounds (ctx : List Bool) (k : ℕ) :
    (CoefficientMarkedRecordTraceCutMetadata.header hn ht ha ctx k).choice ≤
      2^(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width ctx ∧
    (CoefficientMarkedRecordTraceCutMetadata.header hn ht ha ctx k).degree ≤
      2^(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width ctx := by
  let hR := BinaryFn.const 0
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  let key := CoefficientMarkedRecordRowLayout.key (n := n) ctx k (BinaryNatCode.encode 2)
  have h := bounds B.parameters B.plan B.data key
  have hs := CoefficientMarkedRecordSelectedMetadata.selected_header hn ht ha hR key
  dsimp only [B] at h
  rw [hs] at h
  have hr : pairFst key = ctx := CoefficientMarkedRecordRowLayout.key_root (n := n) ctx k (BinaryNatCode.encode 2)
  rw [hr] at h
  exact h

theorem cap_eq {R : List Bool → ℕ} (hR : BinaryFn R) (ctx w : List Bool) (j : ℕ) :
    IntegralFramedTraceCutGuards.cap (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
      (IntegralFramedTraceCutScan.stagePacket (pair ctx w) j) =
      2^(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width ctx := by
  rw [cap_stage]
  rfl

end LeanCanny.Encoding.CoefficientMarkedRecordTraceGuardMetadata
