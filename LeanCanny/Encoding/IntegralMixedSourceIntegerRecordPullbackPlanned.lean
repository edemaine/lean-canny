/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullbackBounds
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPlanned
/-! # Planning before root projection, with explicit literal Plan/Data codomains -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullback
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
open IntegralMixedFramedNormalizationBits (planned plannedPlan plannedData planned_access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem source_snapshot_planned (p : Parameters) (script : Plan p) (R : BoundedFullWriter.Readers)
    (s : BoundedRegularFramedOriginalBits.Snapshot p script R) (L F C : List Bool→ℕ) :
    BoundedRegularFramedOriginalBits.Snapshot (planned p L F C) (plannedPlan p script L F C) R := ⟨s.ambient,s.source⟩

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ)
  (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (S root 0).degree≤2^P.width root)
  (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
  (hW : ∀root,(P.degree root).size≤P.sourceWidth root)
  (project : List Bool→List Bool) (extra : List Bool→ℕ)
local notation "D" => IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom
local notation "J" => IntegralMixedSourceIntegerRecordAppend.data P S hn hd hcap N hq T hz hT hroom hW

noncomputable def plannedCallerControls (a : Access P) (hN : UnaryFn N) (hA : IntegerPolynomialRootQueriesBits.Access T)
    (hp : project∈FP) (he : BinaryFn extra)
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime)
    (scope : ∀key,(ETR.TermView.term (R.source key)).arity≤R.dim key)
    (s : BoundedRegularFramedOriginalBits.Snapshot P D R)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) :
    IntegralMixedFramedCurrentQNativeBits.Controls
      (IntegralMixedFramedRootPullback.parameters (planned P L F C) project extra)
      (IntegralMixedFramedRootPullback.plan (planned P L F C) (plannedPlan P D L F C) project extra)
      (IntegralMixedFramedRootPullback.data (planned P L F C) (plannedPlan P D L F C) (plannedData P D J L F C) project extra) :=
  currentQControls (planned P L F C) S hn hd hcap N hq T hz hT hroom hW project extra
    (planned_access P a hL hF hC) hN hA hp he R hR scope
    (source_snapshot_planned P D R s L F C) L F C hL hF hC

theorem plannedCallerBounds (a : Access P) (hN : UnaryFn N) (hA : IntegerPolynomialRootQueriesBits.Access T)
    (hp : project∈FP) (he : BinaryFn extra)
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime)
    (scope : ∀key,(ETR.TermView.term (R.source key)).arity≤R.dim key)
    (s : BoundedRegularFramedOriginalBits.Snapshot P D R)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (hi : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hf : ∀root,1≤F root) (hl : ∀root,1≤L root) :
    IntegralMixedFramedCurrentQNativeBits.Bounds
      (IntegralMixedFramedRootPullback.parameters (planned P L F C) project extra)
      (IntegralMixedFramedRootPullback.plan (planned P L F C) (plannedPlan P D L F C) project extra)
      (IntegralMixedFramedRootPullback.data (planned P L F C) (plannedPlan P D L F C) (plannedData P D J L F C) project extra)
      (plannedCallerControls P S hn hd hcap N hq T hz hT hroom hW project extra a hN hA hp he R hR scope s L F C hL hF hC) :=
  currentQBounds (planned P L F C) S hn hd hcap N hq T hz hT hroom hW project extra
    (planned_access P a hL hF hC) hN hA hp he R hR scope (source_snapshot_planned P D R s L F C) L F C hL hF hC
    (IntegralMixedFramedNormalizationBits.planned_familyInputs P D L F C hi) hf hl
    (IntegralMixedFramedNormalizationBits.planned_budget P L F C)

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullback
