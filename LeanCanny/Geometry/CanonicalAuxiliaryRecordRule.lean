/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryLimitCut
public import LeanCanny.Geometry.CanonicalAuxiliarySeededSampling
/-! # Each correlated geometric cut has its literal original unit record -/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.ETR IntegralMixedHistory
open IntegralMixedCanonicalDilation IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem critical_ext {N : ℕ} (r s : CriticalRule N)
    (ho : r.offset=s.offset) (hj : r.objective=s.objective) (hc : r.coordinate=s.coordinate)
    (hs : r.scales=s.scales) (hh : r.heights=s.heights) : r=s := by
  cases r
  cases s
  cases ho
  cases hj
  cases hc
  cases hs
  cases hh
  rfl

private theorem sweep_ext {N : ℕ} (r s : Rule N)
    (hr : r.critical=s.critical) (hh : r.height=s.height) (hs : r.slope=s.slope) : r=s := by
  cases r
  cases s
  cases hr
  cases hh
  cases hs
  rfl

variable {n S B D : ℕ} {t : Term} {ht : (AuxiliaryTiltedTerm.term n t).degreeBound≤D}

theorem SampleFrame.criticalRule_front (F : SampleFrame n S B D t ht) (hF : F.Front) :
    F.criticalRule=IntegralMixedCanonicalDilation.rule (n:=n+1) (F.frozen_le.trans (Nat.le_succ n))
      (frontSelector F.frozen 0) := by
  apply sweep_ext
  · apply critical_ext
    · rfl
    · rfl
    · rfl
    · rfl
    · funext i
      change heightExpr F.selector i=heightExpr (frontSelector F.frozen 0) i
      unfold heightExpr
      split_ifs with h0 hi
      · rfl
      · congr 1
        exact hF _
      · rfl
  · rfl
  · rfl

theorem SampleFrame.coordinate_zero (F : SampleFrame n S B D t ht) : (F.coordinate).val=0 := by
  change F.frozen-F.frozen=0
  omega

private theorem cut_at_zero {N W : ℕ} (P : SpatialSource N) (r s : Rule N) (hrs : r=s)
    (j : Fin (N-r.critical.offset.val+1)) (hj : j.val=0) (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound P r))
    (hc : c.val<IntegralMixedLimitCoordinate.ChoiceBound P s) (d : ℕ)
    (ha : d≤IntegralMixedExceptionalBounds.auxiliaryCap (N+1) P.degree) (hd : d≤2^W) :
    (IntegralMixedFullHistoryScript.Command.cut r (.limitCoordinate j c) d ha hd : IntegralMixedFullHistoryScript.Command P W) =
      .cut s (.limitCoordinate ⟨0,Nat.succ_pos _⟩ ⟨c.val,hc⟩) d ha hd := by
  cases hrs
  have HJ : j=0 := Fin.ext hj
  cases HJ
  rfl

theorem SampleFrame.record_command (F : SampleFrame n S B D t ht) (hF : F.Front)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound
      (source F.frozen D t ht F.birth B F.height) F.criticalRule))
    (d : ℕ) (hd : d≤IntegralMixedLimitCoordinate.degree (source F.frozen D t ht F.birth B F.height) F.criticalRule) :
    IntegralMixedCanonicalUnitRuleBits.command (source F.frozen D t ht F.birth B F.height) (by omega) F.frozen
      (IntegralMixedAuxiliaryLimitRecord.record n F.frozen 0 c.val d)
      (by change IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B; exact hcap) =
      IntegralMixedLimitCoordinate.command F.state F.criticalRule F.coordinate c d hd := by
  have HR := F.criticalRule_front hF
  have HC : c.val<IntegralMixedLimitCoordinate.ChoiceBound
      (source F.frozen D t ht F.birth B F.height)
      (IntegralMixedCanonicalDilation.rule (n:=n+1) (F.frozen_le.trans (Nat.le_succ n)) (frontSelector F.frozen 0)) := by
    rw [←HR]
    exact c.isLt
  have HA := hd.trans (IntegralMixedLimitCoordinate.degree_auxiliaryCap
    (source F.frozen D t ht F.birth B F.height) F.criticalRule)
  have HP : IntegralMixedExceptionalBounds.auxiliaryCap (n+3)
      (source F.frozen D t ht F.birth B F.height).degree≤2^B := hcap
  have H := IntegralMixedAuxiliaryLimitRecord.cut_dilation (source F.frozen D t ht F.birth B F.height)
    F.frozen 0 c.val d F.frozen_le HP HC HA
  have Hcut := cut_at_zero (source F.frozen D t ht F.birth B F.height) _ _ HR F.coordinate F.coordinate_zero
    c HC d HA (hd.trans (IntegralMixedLimitCoordinate.degree_cap F.state F.criticalRule))
  simpa only [Nat.zero_add,IntegralMixedLimitCoordinate.command] using H.trans Hcut.symm
end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
