/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceRawGuards
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutInstalled
public import LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientOnly
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceStageBinding
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutWordTuple
/-! # Whole coefficient-only interval guards on the OWN full-row curve -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutCoefficientGuards
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem same_descriptor (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (ctx w : List Bool) (j : ℕ) :
    IntegralFramedTraceCutGuards.choice P D H (pair (pair ctx []) (List.replicate j true)) =
      IntegralFramedTraceCutGuards.choice P D H (IntegralFramedTraceCutScan.stagePacket (pair ctx w) j) ∧
    IntegralFramedTraceCutGuards.degree P D H (pair (pair ctx []) (List.replicate j true)) =
      IntegralFramedTraceCutGuards.degree P D H (IntegralFramedTraceCutScan.stagePacket (pair ctx w) j) := by
  simp only [IntegralFramedTraceCutGuards.choice, IntegralFramedTraceCutGuards.degree,
    IntegralFramedTraceCutGuards.parent, Function.comp_apply, IntegralFramedTraceCutGuards.descriptor,
    IntegralFramedTraceCutGuards.root, IntegralFramedTraceCutScan.stagePacket, pairFst_pair, pairSnd_pair, and_self]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
local notation "CTX" => CoefficientMarkedRecordFullCutInstalled.context (n := n)

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedPhysicalMarkedPlan.bank

theorem choice (ctx w : List Bool) (k left right : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    IntegralMixedPhysicalCutLocalGuards.choice hn ht ha hR false (pair (CTX ctx k left right) w) =
      (CoefficientMarkedRecordTraceCutMetadata.header hn ht ha ctx k).choice := by
  unfold IntegralMixedPhysicalCutLocalGuards.choice
  simp only [IntegralMixedPhysicalCutOpenInterval.guardContext, IntegralMixedPhysicalCutOpenInterval.birthWord,
    CoefficientMarkedRecordFullCutInstalled.context, pairFst_pair, pairSnd_pair]
  exact (same_descriptor (B).parameters (B).plan (B).data ctx w (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)).1.trans
    (CoefficientMarkedRecordTraceCutMetadata.choice hn ht ha hR ctx w k hk)

theorem degree (ctx w : List Bool) (k left right : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    IntegralMixedPhysicalCutOpenInterval.degree hn ht ha hR false (CTX ctx k left right) =
      (CoefficientMarkedRecordTraceCutMetadata.header hn ht ha ctx k).degree := by
  unfold IntegralMixedPhysicalCutOpenInterval.degree
  simp only [Function.comp_apply, IntegralMixedPhysicalCutOpenInterval.guardContext, IntegralMixedPhysicalCutOpenInterval.birthWord,
    CoefficientMarkedRecordFullCutInstalled.context, pairFst_pair, pairSnd_pair]
  exact (same_descriptor (B).parameters (B).plan (B).data ctx w (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)).2.trans
    (CoefficientMarkedRecordTraceCutMetadata.degree hn ht ha hR ctx w k hk)

theorem cap (ctx w : List Bool) (k left right : ℕ) :
    IntegralMixedPhysicalCutLocalGuards.cap (B).parameters (pair (CTX ctx k left right) w) =
      2^(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width ctx := by
  simp only [IntegralMixedPhysicalCutLocalGuards.cap, CoefficientMarkedRecordFullCutInstalled.context, pairFst_pair]
  have H := CoefficientMarkedRecordTraceGuardMetadata.cap_eq hn ht ha hR ctx w 0
  simpa only [IntegralFramedTraceCutGuards.cap, IntegralFramedTraceCutGuards.root,
    IntegralFramedTraceCutScan.stagePacket, pairFst_pair] using H

/-- Every range check and the actual creating-cut classification is original
metadata; the sampled word is absent from this exact characterization. -/
theorem bounds_iff (ctx w : List Bool) (k left right : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    IntegralMixedPhysicalCutOpenInterval.Bounds hn ht ha hR false (pair (CTX ctx k left right) w) ↔
      left < IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx ∧
      right < IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx ∧
      CoefficientMarkedRecordCutSource.birth (n := n) ctx k < IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx ∧
      IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false := by
  have HS : IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha hR false
      (IntegralMixedPhysicalCutOpenInterval.guardPacket (pair (CTX ctx k left right) w)) ↔
        IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false := by
    simpa only [IntegralMixedPhysicalCutOpenInterval.guardPacket, IntegralMixedPhysicalCutOpenInterval.birthWord,
      CoefficientMarkedRecordFullCutInstalled.context, IntegralFramedTraceCutScan.stagePacket, pairFst_pair, pairSnd_pair] using
      CoefficientMarkedRecordTraceStageBinding.raw_cut_iff hn ht ha hR ctx w k hk
  unfold IntegralMixedPhysicalCutOpenInterval.Bounds
  rw [HS]
  simp only [pairFst_pair, CoefficientMarkedRecordFullCutInstalled.context_selected,
    Bool.false_eq_true, ite_false, ite_true]
  unfold IntegralMixedPhysicalCutOpenInterval.count
  rw [CoefficientMarkedRecordFullCutWordTuple.terminal_count hn ht ha hR ctx k left right]
  simp only [IntegralMixedPhysicalCutOpenInterval.birthWord, CoefficientMarkedRecordFullCutInstalled.context,
    pairFst_pair, pairSnd_pair, List.length_replicate]

attribute [local irreducible] SquareSampleCompleteVertices.Valid SquareSampleCompleteVertices.candidate

variable {S : List Bool → ℕ} (hS : BinaryFn S)

/-- Lower-choice vanishing, leading survival, every higher coefficient and
the constant final head are transported together, with no guard premise. -/
theorem guards_on_curve (ctx : List Bool)
    (hRlarge : CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx ≤ R ctx)
    (hSlarge : CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx ≤ S ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordFullCutSign.count hn ht ha ctx) → ℝ))
    (hx : ∀ y : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl y.val (x y))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R ctx) (hv : v.val = (2 : ℝ)^S ctx)
    (k left right : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (wR wS : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) wR)
    (hwS : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (CTX ctx k left right) wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (CTX ctx k left right) wS hwS).val (x v)) :
    IntegralMixedPhysicalCutCoefficientOnly.Guards hn ht ha hR false (pair (CTX ctx k left right) wR) ↔
      IntegralMixedPhysicalCutCoefficientOnly.Guards hn ht ha hS false (pair (CTX ctx k left right) wS) := by
  apply FiniteCoefficientGuardTransport.guards_iff
  · rw [choice hn ht ha hR ctx wR k left right hk, choice hn ht ha hS ctx wS k left right hk]
  · simp only [Function.comp_apply, pairFst_pair]
    rw [degree hn ht ha hR ctx wR k left right hk, degree hn ht ha hS ctx wS k left right hk]
  · rw [cap hn ht ha hR, cap hn ht ha hS]
  · simp only [Function.comp_apply, pairFst_pair]
    rw [degree hn ht ha hR ctx wR k left right hk, cap hn ht ha hR]
    exact (CoefficientMarkedRecordTraceGuardMetadata.header_bounds hn ht ha ctx k).2
  · intro e he requested hrequested
    rw [cap hn ht ha hR] at he
    rw [choice hn ht ha hR ctx wR k left right hk] at hrequested
    have hr := hrequested.trans (CoefficientMarkedRecordTraceGuardMetadata.header_bounds hn ht ha ctx k).1
    rw [IntegralMixedPhysicalCutLocalGuards.sign_packet, IntegralMixedPhysicalCutLocalGuards.sign_packet]
    dsimp only [CoefficientMarkedRecordFullCutInstalled.context] at hwR hwS hjR hjS
    have H := CoefficientMarkedRecordTraceProbeSign.value_on_curve hn ht ha ctx hR hS hRlarge hSlarge
      ha0 x hx u v hu hv
      (pair (List.replicate (CoefficientMarkedRecordCutSource.birth (n := n) ctx k) true)
        (pair (BinaryNatCode.encode left) (BinaryNatCode.encode right)))
      (pair (List.replicate (CoefficientMarkedRecordCutSource.birth (n := n) ctx k) true)
        (pair (BinaryNatCode.encode left) (BinaryNatCode.encode right)))
      wR wS hwR hwS hjR hjS ⟨k, hk, hc, requested, e⟩ he hr
    simpa only [CoefficientMarkedRecordFullCutInstalled.context, IntegralMixedPhysicalCutOpenInterval.birthWord,
      pairFst_pair, pairSnd_pair] using H
  · rfl

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutCoefficientGuards
