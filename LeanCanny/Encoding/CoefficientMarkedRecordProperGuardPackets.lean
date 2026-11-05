/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperComparison
public import LeanCanny.Encoding.CoefficientMarkedRecordProperGuardMetadata
/-! # Literal native guarded Near/Rank packets from their five own statistics -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordProperGuardPackets
open LeanCanny.Algebra LeanCanny.Computation Set
open IntegralMixedRoadmapProperRow CoefficientMarkedRecordProperWordValue
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed

theorem near_guard_iff (right : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (w code : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR false) z w) :
    pair (pair z w) code ∈ nearLanguage hn ht ha hR right ↔
      OrderedWindowStatisticBits.Accept (OrderedWindowStatisticBits.pack code
        (SignStatisticBits.integerCode (nearStatistic hn ht ha hR right 0 right false z w))
        (SignStatisticBits.integerCode (nearStatistic hn ht ha hR right 2 right false z w))
        (SignStatisticBits.integerCode (nearStatistic hn ht ha hR right 1 right false z w))
        (SignStatisticBits.integerCode (nearStatistic hn ht ha hR right 2 right true z w))
        (SignStatisticBits.integerCode (nearStatistic hn ht ha hR right 1 right true z w))) := by
  have HM := CoefficientMarkedRecordProperGuardMetadata.near_metadata hn ht ha hR right z hc hg
  change _ ∈ IntegralFramedPhysicalNear.guarded (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (parent hn ht ha hR false) (terminal hn ht ha hR false) (centerIndex hn ht ha hR right)
    (pointIndex hn ht ha hR false false) (positive hn ht ha hR false)
    (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR) false)
    (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR) false) right ↔ _
  rw [IntegralFramedPhysicalNear.guarded_packet _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM hv]
  simp only [IntegralFramedPhysicalNear.Accept, Set.mem_ofPred_eq, IntegralFramedPhysicalNear.packet,
    IntegralFramedPhysicalNear.reset, pairFst_pair, pairSnd_pair]
  rfl

theorem rank_guard_iff (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (w code : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR true) z w) :
    pair (pair z w) code ∈ rankLanguage hn ht ha hR ↔
      OrderedWindowStatisticBits.Accept (OrderedWindowStatisticBits.pack code
        (SignStatisticBits.integerCode (rankStatistic hn ht ha hR 0 false z w))
        (SignStatisticBits.integerCode (rankStatistic hn ht ha hR 2 false z w))
        (SignStatisticBits.integerCode (rankStatistic hn ht ha hR 1 false z w))
        (SignStatisticBits.integerCode (rankStatistic hn ht ha hR 2 true z w))
        (SignStatisticBits.integerCode (rankStatistic hn ht ha hR 1 true z w))) := by
  have HM := CoefficientMarkedRecordProperGuardMetadata.rank_metadata hn ht ha hR z hc hg
  simp only [rankLanguage, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, HM, hv, true_and]
  simp only [RankAccept, rankPacket, IntegralFramedPhysicalNear.reset, pairFst_pair, pairSnd_pair]
  rfl

/-- The literal complete native guard is preserved, including Metadata and
the five ordered-window statistics, without target Atomic.Valid. -/
theorem near_guard_on_curve (right : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
    (hRlarge : CoefficientMarkedRecordProperPrincipalSign.cutoff hn ht ha false right z ≤
      IntegralMixedOriginalRegularSource.radius R (catalogRoot n false z))
    (hSlarge : CoefficientMarkedRecordProperPrincipalSign.cutoff hn ht ha false right z ≤
      IntegralMixedOriginalRegularSource.radius S (catalogRoot n false z))
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordProperPrincipalSign.cutoff hn ht ha false right z ≤ a)
    (x : C(Ioo a b, Fin (properPhysicalData hn ht ha false z).count → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (catalogRoot n false z)
      (IntegralMixedCausalRecordPlanBits.count (catalogRoot n false z)) le_rfl u.val (x u))
    (u v : Ioo a b)
    (hu : u.val = (2 : ℝ)^IntegralMixedOriginalRegularSource.radius R (catalogRoot n false z))
    (hv : v.val = (2 : ℝ)^IntegralMixedOriginalRegularSource.radius S (catalogRoot n false z))
    (wR wS code : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR false) z wR)
    (hwS : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hS false) z wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR false) z wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hS false) z wS hwS).val (x v)) :
    pair (pair z wR) code ∈ nearLanguage hn ht ha hR right ↔
      pair (pair z wS) code ∈ nearLanguage hn ht ha hS right := by
  rw [near_guard_iff hn ht ha hR right z hc hg wR code hwR,
    near_guard_iff hn ht ha hS right z hc hg wS code hwS]
  have H (power : Fin 3) (eps : Bool) :=
    CoefficientMarkedRecordProperComparison.near_statistic_on_curve hn ht ha right power right eps z hc hg hR hS
      hRlarge hSlarge ha0 x hx u v hu hv wR wS hwR hwS hjR hjS
  rw [H 0 false, H 2 false, H 1 false, H 2 true, H 1 true]

/-- The literal complete native guard is preserved, including Metadata and
the five ordered-window statistics, without target Atomic.Valid. -/
theorem rank_guard_on_curve (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
    (hRlarge : CoefficientMarkedRecordProperPrincipalSign.cutoff hn ht ha true false z ≤
      IntegralMixedOriginalRegularSource.radius R (catalogRoot n true z))
    (hSlarge : CoefficientMarkedRecordProperPrincipalSign.cutoff hn ht ha true false z ≤
      IntegralMixedOriginalRegularSource.radius S (catalogRoot n true z))
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordProperPrincipalSign.cutoff hn ht ha true false z ≤ a)
    (x : C(Ioo a b, Fin (properPhysicalData hn ht ha true z).count → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (catalogRoot n true z)
      (IntegralMixedCausalRecordPlanBits.count (catalogRoot n true z)) le_rfl u.val (x u))
    (u v : Ioo a b)
    (hu : u.val = (2 : ℝ)^IntegralMixedOriginalRegularSource.radius R (catalogRoot n true z))
    (hv : v.val = (2 : ℝ)^IntegralMixedOriginalRegularSource.radius S (catalogRoot n true z))
    (wR wS code : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR true) z wR)
    (hwS : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hS true) z wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR true) z wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hS true) z wS hwS).val (x v)) :
    pair (pair z wR) code ∈ rankLanguage hn ht ha hR ↔
      pair (pair z wS) code ∈ rankLanguage hn ht ha hS := by
  rw [rank_guard_iff hn ht ha hR z hc hg wR code hwR,
    rank_guard_iff hn ht ha hS z hc hg wS code hwS]
  have H (power : Fin 3) (eps : Bool) :=
    CoefficientMarkedRecordProperComparison.rank_statistic_on_curve hn ht ha power eps z hc hg hR hS
      hRlarge hSlarge ha0 x hx u v hu hv wR wS hwR hwS hjR hjS
  rw [H 0 false, H 2 false, H 1 false, H 2 true, H 1 true]

end LeanCanny.Encoding.CoefficientMarkedRecordProperGuardPackets
