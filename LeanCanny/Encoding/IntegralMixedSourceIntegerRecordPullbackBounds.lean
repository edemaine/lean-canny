/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullbackNative
public import LeanCanny.Algebra.BoundedRegularIntegerCurrentQRootControls
/-! # Caller-modulus augmentation retains the original derived script bounds -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullback
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

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
local notation "B" => IntegralMixedSourceIntegerRecordAppend.base P S hd hcap N T hz hT hroom
local notation "OR" => IntegralMixedSourceIntegerRecordAppend.originalRecords P S hn hd hcap N hq T hz hT
local notation "ROOM" => IntegralMixedSourceIntegerRecordAppend.records_room P S hn hd hcap N hq T hz hT hroom
local notation "DEG" => IntegralMixedSourceIntegerRecordAppend.originalRecords_degree P S hn hd hcap N hq T hz hT
local notation "PP" => IntegralMixedFramedRootPullback.parameters P project extra
local notation "DD" => IntegralMixedFramedRootPullback.plan P D project extra
local notation "JJ" => IntegralMixedFramedRootPullback.data P D J project extra

private theorem fallback_rule (key : List Bool) : ((JJ).fallback key).rule=
    IntegralMixedCausalPlanBits.fallbackRule ((PP).ambient (pairFst key)) (hn (project (pairFst key))) := by
  have HE : IntegralMixedCausalPlanBits.data PP (IntegralMixedFramedRootPullback.plan P B project extra)
      (fun root=>OR (project root)) (fun root=>ROOM (project root))
      (fun root=>hn (project root)) (fun root=>DEG (project root)) (fun root=>hW (project root))=JJ :=
    IntegralMixedCausalPlanBits.data_pullback P B OR ROOM hn DEG hW project extra
  exact (congrArg (fun j:IntegralMixedFramedHistoryFamilyBits.Data PP DD=>(j.fallback key).rule) HE).symm

theorem fallback_bounds (L C : List Bool→ℕ) (hL : ∀root,1≤L root) (key : List Bool) :
    IntegralMixedFramedOriginalBounds.FallbackBounds PP DD JJ (L∘project) (C∘project) key := by
  have HB : IntegralMixedFullHeightBits.RuleBounds (C (project (pairFst key))+1) (L (project (pairFst key)))
      (IntegralMixedCausalPlanBits.fallbackRule ((PP).ambient (pairFst key)) (hn (project (pairFst key)))) := by
    refine ⟨?_,?_,?_,?_⟩
    · exact fun _=>hL _
    · exact fun _=>Nat.zero_le _
    · intro i
      simpa only [IntegralMixedCausalPlanBits.fallbackRule,Int.natAbs_one,Nat.size_one] using
        Nat.succ_le_succ (Nat.zero_le (C (project (pairFst key))))
    · simpa only [IntegralMixedCausalPlanBits.fallbackRule,Int.natAbs_one,Nat.size_one] using
        Nat.succ_le_succ (Nat.zero_le (C (project (pairFst key))))
  unfold IntegralMixedFramedOriginalBounds.FallbackBounds
  cases (instruction PP DD key).command <;> first | trivial | simpa only [fallback_rule,Function.comp_apply] using HB

theorem currentQBounds (a : Access P) (hN : UnaryFn N) (hA : IntegerPolynomialRootQueriesBits.Access T)
    (hp : project∈FP) (he : BinaryFn extra)
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime)
    (scope : ∀key,(ETR.TermView.term (R.source key)).arity≤R.dim key)
    (s : BoundedRegularFramedOriginalBits.Snapshot P D R)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (hi : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hf : ∀root,1≤F root) (hl : ∀root,1≤L root)
    (hb : ∀root,IntegralMixedFramedNormalizationBits.requiredModulus P L F C root≤P.modulusBound root) :
    IntegralMixedFramedCurrentQNativeBits.Bounds PP DD JJ
      (currentQControls P S hn hd hcap N hq T hz hT hroom hW project extra a hN hA hp he R hR scope s L F C hL hF hC) where
  original:=IntegralMixedFramedRootPullback.familyInputs P D project extra L F C hi
  factor root:=hf (project root)
  fallback:=fallback_bounds P S hn hd hcap N hq T hz hT hroom hW project extra L C hl
  modulus root:=by
    change IntegralMixedFramedNormalizationBits.requiredModulus PP (L∘project) (F∘project) (C∘project) root≤
      max (P.modulusBound (project root)) (extra root)
    rw [BoundedRegularIntegerCurrentQBits.requiredModulus_pullback]
    exact (hb (project root)).trans (le_max_left _ _)

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullback
