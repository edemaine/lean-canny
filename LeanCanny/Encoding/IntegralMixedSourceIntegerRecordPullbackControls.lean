/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullbackSnapshot
/-! # Original rule costs and charged slopes at projected caller roots -/
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

noncomputable def slopeAdapter (a : Access P) (hN : UnaryFn N) (hp : project∈FP) (he : BinaryFn extra) :
    IntegralMixedFramedCurrentQHeightBits.UnitSlope PP DD JJ := by
  have HM : IntegralMixedCausalPlanBits.modeWords P OR∈FP :=
    mem_FP_of_eq (IntegralMixedSourceIntegerRecordAppend.modeTable_FP P a hN)
      (fun root=>(IntegralMixedSourceIntegerRecordAppend.modeWords_eq P S hn hd hcap N hq T hz hT root).symm)
  have HC:=IntegralMixedCausalPlanBits.metadata_pullback P OR project extra a hp he HM
  have HU:=IntegralMixedCausalPlanBits.unitSlope PP (IntegralMixedFramedRootPullback.plan P B project extra)
    (fun root=>OR (project root)) (fun root=>ROOM (project root))
    (fun root=>hn (project root)) (fun root=>DEG (project root)) (fun root=>hW (project root))
    (IntegralMixedFramedRootPullback.access P a project hp extra he) HC
  have HE : IntegralMixedCausalPlanBits.data PP (IntegralMixedFramedRootPullback.plan P B project extra)
      (fun root=>OR (project root)) (fun root=>ROOM (project root))
      (fun root=>hn (project root)) (fun root=>DEG (project root)) (fun root=>hW (project root))=JJ :=
    IntegralMixedCausalPlanBits.data_pullback P B OR ROOM hn DEG hW project extra
  rw [HE] at HU
  exact HU

noncomputable def originalRules (a : Access P) (hN : UnaryFn N) (hp : project∈FP) (he : BinaryFn extra) :
    IntegralMixedFramedCurrentQIndexedBits.OriginalRules PP DD JJ where
  word:=word P N project extra
  word_space:=SpaceFunction.ofFP _ (word_FP P N project extra a hN hp he)
  word_eq:=word_eq P S hn hd hcap N hq T hz hT hroom hW project extra
  physicalMask:=mask P N project extra true
  virtualMask:=mask P N project extra false
  physical_FP:=mask_FP P N project extra a hN hp he true
  virtual_FP:=mask_FP P N project extra a hN hp he false
  physicalScales q i:=physical_mask P S hn hd hcap N hq T hz hT hroom project extra
    (IntegralMixedVirtualTaskBits.saved PP q) i.val i.isLt
  virtualScales q i:=virtual_mask P S hn hd hcap N hq T hz hT hroom hW project extra
    (IntegralMixedVirtualTaskBits.saved PP q) i.val i.isLt
  slope:=slopeAdapter P S hn hd hcap N hq T hz hT hroom hW project extra a hN hp he

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullback
