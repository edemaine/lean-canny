/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipal
/-! # Actual ordinary and mean principal components specialize literally -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR Polynomial
open CoefficientTarskiParameterQueries CoefficientTarskiZeroParameterQueries
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedRecordPlan (certifiedParameters certifiedPlan certifiedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R0 : List Bool → ℕ} (hR0 : BinaryFn R0)
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed

theorem proper_near_head_map (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n false z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)) :
    HEq ((properNearHead hn ht ha right eta z hc).map (MvPolynomial.map
      (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)))))
      ((nearFamily hn ht ha hR0 right power eta eps).head z) := by
  have HM := proper_shifted_head_specializes hn ht ha hR0 right eta z hc hg hR
  have HI := funext (principal_center_index hn ht ha hR0 right)
  rw [← HI] at HM
  have HA := (principal_terminal_count hn ht ha hR0 false z).symm
  unfold properNearHead
  rw [pairLift_map]
  have HP := pair_heq true _ _ HA HM
  dsimp only [nearFamily, IntegralFramedTerminalTarskiStatistic.mf,
    IntegralMixedFramedTerminalTarskiFamilyBits.family, IntegralMixedFramedTerminalTarskiFamilyBits.head,
    IntegralMixedFramedTerminalTarskiFamilyBits.arity, FixedWidthBivariateParameterPairBits.lift]
  dsimp only [pairLift] at HP
  exact HP

theorem proper_near_query_map (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n false z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)) :
    HEq ((properNearQuery hn ht ha power eps z).map (MvPolynomial.map
      (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)))))
      ((nearFamily hn ht ha hR0 right power eta eps).query z) := by
  have HM := proper_point_window_specializes hn ht ha hR0 false eps z hR
  have HA := (principal_terminal_count hn ht ha hR0 false z).symm
  unfold properNearQuery
  rw [Polynomial.map_pow, pairLift_map]
  have HP := pair_heq false _ _ HA HM
  have HQ := polynomial_pow_heq _ _ (congrArg (fun m => 1+(m+1)) HA) HP power.val
  dsimp only [nearFamily, IntegralFramedTerminalTarskiStatistic.mf,
    IntegralMixedFramedTerminalTarskiFamilyBits.family, IntegralMixedFramedTerminalTarskiFamilyBits.query,
    IntegralMixedFramedTerminalTarskiFamilyBits.baseQuery, IntegralMixedFramedTerminalTarskiFamilyBits.arity,
    FixedWidthBivariateParameterPairBits.lift]
  dsimp only [pairLift] at HQ
  exact HQ

theorem proper_rank_head_map (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n true z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n true z)) :
    HEq ((properRankHead hn ht ha z hc).map (MvPolynomial.map
      (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n true z)))))
      ((rankFamily hn ht ha hR0 power eps).head z) := by
  have HM := proper_terminal_cast_specializes hn ht ha hR0 true z hc hg hR
  have HA := (principal_terminal_count hn ht ha hR0 true z).symm
  unfold properRankHead
  rw [zeroHead_map]
  have HP := zeroHead_heq _ _ HA HM
  dsimp only [rankFamily, IntegralFramedZeroTarskiStatistic.mf, IntegralMixedFramedZeroTarskiBits.family,
    IntegralMixedFramedZeroTarskiBits.head, IntegralMixedFramedZeroTarskiBits.arity,
    FixedWidthBivariateZeroLiftBits.head, FixedWidthBivariateZeroLiftBits.liftHom,
    FixedWidthBivariateZeroLiftBits.zeroHom]
  dsimp only [zeroHead, zeroHom] at HP
  exact HP

theorem proper_rank_query_map (power : Fin 3) (eps : Bool) (z : List Bool)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n true z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n true z)) :
    HEq ((properRankQuery hn ht ha power eps z).map (MvPolynomial.map
      (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n true z)))))
      ((rankFamily hn ht ha hR0 power eps).query z) := by
  have HM := proper_point_window_specializes hn ht ha hR0 true eps z hR
  have HA := (principal_terminal_count hn ht ha hR0 true z).symm
  unfold properRankQuery
  rw [Polynomial.map_pow, epsilonHead_map]
  have HP := epsilonHead_heq _ _ HA HM
  have HQ := polynomial_pow_heq _ _ (congrArg (fun m => m+2) HA) HP power.val
  dsimp only [rankFamily, IntegralFramedZeroTarskiStatistic.mf, IntegralMixedFramedZeroTarskiBits.family,
    IntegralMixedFramedZeroTarskiBits.query, IntegralMixedFramedZeroTarskiBits.baseQuery,
    IntegralMixedFramedZeroTarskiBits.arity, FixedWidthBivariateZeroLiftBits.epsilonHead]
  dsimp only [epsilonHead] at HQ
  exact HQ

theorem proper_near_principal_map (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n false z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)) (j : ℕ) :
    HEq (MvPolynomial.map
      (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)))
      (properNearPrincipal hn ht ha right power eta eps z hc j))
      (FixedWidthTarskiPrincipalBits.polynomial (nearFamily hn ht ha hR0 right power eta eps) z j) := by
  let F := nearFamily hn ht ha hR0 right power eta eps
  let d := max 1 (catalogDegree hn ht ha false z)
  have HG := (rank_row_good_iff hn ht ha hR0 z).mpr hg
  have HD := near_degree_catalog_of_count hn ht ha hR0 z hc HG
  have HA : 1+(IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n false z)+1) = F.arity z := by
    exact congrArg (fun m => 1+(m+1)) (principal_terminal_count hn ht ha hR0 false z).symm
  have Hdeg : d = F.degree z := by
    dsimp only [F, d, nearFamily, IntegralFramedTerminalTarskiStatistic.mf,
      IntegralMixedFramedTerminalTarskiFamilyBits.family, IntegralMixedFramedTerminalTarskiFamilyBits.degree]
    rw [HD]
  have Hseed : d-1 = F.seedDegree z := by
    dsimp only [F, d, nearFamily, IntegralFramedTerminalTarskiStatistic.mf,
      IntegralMixedFramedTerminalTarskiFamilyBits.family, IntegralMixedFramedTerminalTarskiFamilyBits.seedDegree, IntegralMixedFramedTerminalTarskiFamilyBits.degree]
    rw [HD]
  have Hbound : d+2 = F.bound z := by
    dsimp only [F, d, nearFamily, IntegralFramedTerminalTarskiStatistic.mf,
      IntegralMixedFramedTerminalTarskiFamilyBits.family, IntegralMixedFramedTerminalTarskiFamilyBits.inputBound,
      IntegralMixedFramedTerminalTarskiFamilyBits.degree]
    rw [HD]
  unfold properNearPrincipal
  rw [principal_map]
  exact principal_heq _ _ (F.head z) (F.query z) d (F.degree z) (d-1) (F.seedDegree z)
    (d+2) (F.bound z) j HA (proper_near_head_map hn ht ha hR0 right power eta eps z hc hg hR)
    (proper_near_query_map hn ht ha hR0 right power eta eps z hR) Hdeg Hseed Hbound

theorem proper_rank_principal_map (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n true z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n true z)) (j : ℕ) :
    HEq (MvPolynomial.map
      (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n true z)))
      (properRankPrincipal hn ht ha power eps z hc j))
      (FixedWidthTarskiPrincipalBits.polynomial (rankFamily hn ht ha hR0 power eps) z j) := by
  let F := rankFamily hn ht ha hR0 power eps
  let d := max 1 (catalogDegree hn ht ha true z)
  have HG := (rank_row_good_iff hn ht ha hR0 z).mpr hg
  have HD := rank_degree_catalog_of_count hn ht ha hR0 z hc HG
  have HA : IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n true z)+2 = F.arity z := by
    exact congrArg (fun m => m+2) (principal_terminal_count hn ht ha hR0 true z).symm
  have Hdeg : d = F.degree z := by
    dsimp only [F, d, rankFamily, IntegralFramedZeroTarskiStatistic.mf,
      IntegralMixedFramedZeroTarskiBits.family, IntegralMixedFramedZeroTarskiBits.degree]
    rw [HD]
  have Hseed : d-1 = F.seedDegree z := by
    dsimp only [F, d, rankFamily, IntegralFramedZeroTarskiStatistic.mf,
      IntegralMixedFramedZeroTarskiBits.family, IntegralMixedFramedZeroTarskiBits.seedDegree, IntegralMixedFramedZeroTarskiBits.degree]
    rw [HD]
  have Hbound : d+2 = F.bound z := by
    dsimp only [F, d, rankFamily, IntegralFramedZeroTarskiStatistic.mf,
      IntegralMixedFramedZeroTarskiBits.family, IntegralMixedFramedZeroTarskiBits.inputBound,
      IntegralMixedFramedZeroTarskiBits.degree]
    rw [HD]
  unfold properRankPrincipal
  rw [principal_map]
  exact principal_heq _ _ (F.head z) (F.query z) d (F.degree z) (d-1) (F.seedDegree z)
    (d+2) (F.bound z) j HA (proper_rank_head_map hn ht ha hR0 power eps z hc hg hR)
    (proper_rank_query_map hn ht ha hR0 power eps z hR) Hdeg Hseed Hbound

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
