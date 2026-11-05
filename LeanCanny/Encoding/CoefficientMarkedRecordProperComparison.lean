/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperWordValue
public import LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalLex
/-! # Actual Near/Rank statistics on separate own words along one root curve -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordProperComparison
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set PrincipalSubresultant
open IntegralMixedRoadmapProperRow
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

/-- Each radius keeps its own actual sampler resources and word. Only the
entire candidate tuples lie on the common physical root curve. -/
theorem near_statistic_on_curve (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
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
    (wR wS : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR false) z wR)
    (hwS : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hS false) z wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR false) z wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hS false) z wS hwS).val (x v)) :
    CoefficientMarkedRecordProperWordValue.nearStatistic hn ht ha hR right power eta eps z wR =
      CoefficientMarkedRecordProperWordValue.nearStatistic hn ht ha hS right power eta eps z wS := by
  have HR := CoefficientMarkedRecordProperWordValue.near_value_eq hn ht ha hR right power eta eps z hc hg
    ((CoefficientMarkedRecordProperPrincipalSign.effective_le hn ht ha false right z).trans hRlarge) wR hwR (x u) hjR
  have HS := CoefficientMarkedRecordProperWordValue.near_value_eq hn ht ha hS right power eta eps z hc hg
    ((CoefficientMarkedRecordProperPrincipalSign.effective_le hn ht ha false right z).trans hSlarge) wS hwS (x v) hjS
  have HV : permanencesMinusVariations ((List.range (max 1 (catalogDegree hn ht ha false z)+1)).reverse.map
      (fun j => RealIteratedTarski.lex (CoefficientMarkedRecordProperPrincipalSeries.near hn ht ha right power eta eps z hc j
        ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R (catalogRoot n false z)) (x u)))) =
    permanencesMinusVariations ((List.range (max 1 (catalogDegree hn ht ha false z)+1)).reverse.map
      (fun j => RealIteratedTarski.lex (CoefficientMarkedRecordProperPrincipalSeries.near hn ht ha right power eta eps z hc j
        ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius S (catalogRoot n false z)) (x v)))) := by
    apply permanencesMinusVariations_congr
    simp only [List.map_map]
    apply List.map_congr_left
    intro j _
    simpa only [Function.comp_apply, hu, hv] using
      CoefficientMarkedRecordProperPrincipalLex.near_lex_on_root_curve hn ht ha right z hc hg ha0 x hx
        power eta eps j u v
  exact HR.trans (HV.trans HS.symm)

/-- Each radius keeps its own actual sampler resources and word. Only the
entire candidate tuples lie on the common physical root curve. -/
theorem rank_statistic_on_curve (power : Fin 3) (eps : Bool) (z : List Bool)
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
    (wR wS : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR true) z wR)
    (hwS : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hS true) z wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR true) z wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hS true) z wS hwS).val (x v)) :
    CoefficientMarkedRecordProperWordValue.rankStatistic hn ht ha hR power eps z wR =
      CoefficientMarkedRecordProperWordValue.rankStatistic hn ht ha hS power eps z wS := by
  have HR := CoefficientMarkedRecordProperWordValue.rank_value_eq hn ht ha hR power eps z hc hg
    ((CoefficientMarkedRecordProperPrincipalSign.effective_le hn ht ha true false z).trans hRlarge) wR hwR (x u) hjR
  have HS := CoefficientMarkedRecordProperWordValue.rank_value_eq hn ht ha hS power eps z hc hg
    ((CoefficientMarkedRecordProperPrincipalSign.effective_le hn ht ha true false z).trans hSlarge) wS hwS (x v) hjS
  have HV : permanencesMinusVariations ((List.range (max 1 (catalogDegree hn ht ha true z)+1)).reverse.map
      (fun j => RealIteratedTarski.lex (CoefficientMarkedRecordProperPrincipalSeries.rank hn ht ha power eps z hc j
        ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R (catalogRoot n true z)) (x u)))) =
    permanencesMinusVariations ((List.range (max 1 (catalogDegree hn ht ha true z)+1)).reverse.map
      (fun j => RealIteratedTarski.lex (CoefficientMarkedRecordProperPrincipalSeries.rank hn ht ha power eps z hc j
        ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius S (catalogRoot n true z)) (x v)))) := by
    apply permanencesMinusVariations_congr
    simp only [List.map_map]
    apply List.map_congr_left
    intro j _
    simpa only [Function.comp_apply, hu, hv] using
      CoefficientMarkedRecordProperPrincipalLex.rank_lex_on_root_curve hn ht ha z hc hg ha0 x hx
        power eps j u v
  exact HR.trans (HV.trans HS.symm)

end LeanCanny.Encoding.CoefficientMarkedRecordProperComparison
