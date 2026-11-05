/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperWordTuple
/-! # Actual Near/Rank statistic readers equal their own principal lists -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordProperWordValue
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial PrincipalSubresultant
open IntegralMixedRoadmapProperRow
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem value_principals (G : FixedWidthTarskiPrincipalBits.Family) (q : List Bool)
    (χ : MvPolynomial (Fin (G.arity q)) ℤ →+* (ℝ[X])[X]) :
    RealIteratedTarski.value ((G.head q).map χ) ((G.query q).map χ) (G.degree q) (G.bound q) (G.seedDegree q) =
      permanencesMinusVariations ((List.range (G.degree q + 1)).reverse.map
        (fun j => RealIteratedTarski.lex (χ (FixedWidthTarskiPrincipalBits.polynomial G q j)))) := by
  unfold RealIteratedTarski.value
  apply congrArg permanencesMinusVariations
  apply List.map_congr_left
  intro j _
  unfold RealIteratedTarski.principal RealIteratedTarski.seed FixedWidthTarskiPrincipalBits.polynomial
  rw [PseudoRemainder.seed_map, signedPsc_map_map]

private theorem pmv_range_congr (d e : ℕ) (f g : ℕ → ℝ) (hd : d = e) (h : ∀ j, f j = g j) :
    permanencesMinusVariations ((List.range (d + 1)).reverse.map f) =
      permanencesMinusVariations ((List.range (e + 1)).reverse.map g) := by
  cases hd
  apply congrArg permanencesMinusVariations
  exact List.map_congr_left (fun j _ => h j)

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R0 : List Bool → ℕ} (hR0 : BinaryFn R0)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed properPhysicalData

noncomputable def nearStatistic (right : Bool) (power : Fin 3) (eta eps : Bool) (z w : List Bool) :=
  IntegralFramedTerminalTarskiStatistic.value (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
    (centerIndex hn ht ha hR0 right) (pointIndex hn ht ha hR0 false false) (positive hn ht ha hR0 false)
    (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
    (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
    power eta eps (pair (pair z w) [])

noncomputable def rankStatistic (power : Fin 3) (eps : Bool) (z w : List Bool) :=
  zeroStatistic hn ht ha hR0 power eps (pair (pair z w) [])

theorem near_principals (right : Bool) (power : Fin 3) (eta eps : Bool) (z w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR0 false) z w) :
    nearStatistic hn ht ha hR0 right power eta eps z w =
      permanencesMinusVariations ((List.range
        ((CoefficientMarkedRecordProperWordTuple.nearInstalled hn ht ha hR0 right power eta eps).degree z + 1)).reverse.map
        (fun j => RealIteratedTarski.lex
          (CoefficientMarkedRecordProperWordTuple.nearNative hn ht ha hR0 right power eta eps z w hv j))) := by
  have HV := IntegralFramedTerminalTarskiStatistic.value_at (B).parameters (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
    (centerIndex hn ht ha hR0 right) (pointIndex hn ht ha hR0 false false) (positive hn ht ha hR0 false)
    (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
    (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
    power eta eps z w hv
  have HM := value_principals (CoefficientMarkedRecordProperWordTuple.nearInstalled hn ht ha hR0 right power eta eps) z
    (IntegralMixedFramedTerminalTarskiSelected.specialization (B).parameters (B).plan (B).data (terminal hn ht ha hR0 false) z
      (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (terminal hn ht ha hR0 false) (positive hn ht ha hR0 false) z w hv))
  exact HV.trans HM

theorem rank_principals (power : Fin 3) (eps : Bool) (z w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR0 true) z w) :
    rankStatistic hn ht ha hR0 power eps z w =
      permanencesMinusVariations ((List.range
        ((CoefficientMarkedRecordProperWordTuple.rankInstalled hn ht ha hR0 power eps).degree z + 1)).reverse.map
        (fun j => RealIteratedTarski.lex
          (CoefficientMarkedRecordProperWordTuple.rankNative hn ht ha hR0 power eps z w hv j))) := by
  have HV := IntegralFramedZeroTarskiStatistic.value_at (B).parameters (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true)
    (pointIndex hn ht ha hR0 true true) (positive hn ht ha hR0 true)
    (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
    (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
    power eps z w hv
  have HM := value_principals (CoefficientMarkedRecordProperWordTuple.rankInstalled hn ht ha hR0 power eps) z
    (MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ)
      (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (terminal hn ht ha hR0 true) (positive hn ht ha hR0 true) z w hv))
  exact HV.trans HM

private theorem near_degree (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z) :
    (CoefficientMarkedRecordProperWordTuple.nearInstalled hn ht ha hR0 right power eta eps).degree z =
      max 1 (catalogDegree hn ht ha false z) := by
  change max 1 (IntegralMixedSelectedCoordinateHead.fullDegree (B).parameters
    (IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data) (parent hn ht ha hR0 false) z) = _
  have HB : B = IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha
      (IntegralMixedOriginalRegularSource.radius_binary hR0) := by
    unfold IntegralMixedPhysicalMarkedPlan.bank
    rfl
  rw [HB]
  exact congrArg (max 1) (near_degree_catalog_of_count hn ht ha hR0 z hc
    ((rank_row_good_iff hn ht ha hR0 z).mpr hg))

private theorem rank_degree (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z) :
    (CoefficientMarkedRecordProperWordTuple.rankInstalled hn ht ha hR0 power eps).degree z =
      max 1 (catalogDegree hn ht ha true z) := by
  change max 1 (IntegralMixedSelectedCoordinateHead.fullDegree (B).parameters
    (IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data) (parent hn ht ha hR0 true) z) = _
  have HB : B = IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha
      (IntegralMixedOriginalRegularSource.radius_binary hR0) := by
    unfold IntegralMixedPhysicalMarkedPlan.bank
    rfl
  rw [HB]
  exact congrArg (max 1) (rank_degree_catalog_of_count hn ht ha hR0 z hc
    ((rank_row_good_iff hn ht ha hR0 z).mpr hg))

/-- Native value_at, the actual declared range and THIS own full tuple yield
the literal formal Near statistic. No degree or interpreting hom is supplied. -/
theorem near_value_eq (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n false z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)) (w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR0 false) z w)
    (raw : Fin (properPhysicalData hn ht ha false z).count → ℝ)
    (hj : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR0 false) z w hv).val raw) :
    nearStatistic hn ht ha hR0 right power eta eps z w =
      permanencesMinusVariations ((List.range (max 1 (catalogDegree hn ht ha false z) + 1)).reverse.map
        (fun j => RealIteratedTarski.lex (CoefficientMarkedRecordProperPrincipalSeries.near hn ht ha right power eta eps z hc j
          ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)) raw))) := by
  apply (near_principals hn ht ha hR0 right power eta eps z w hv).trans
  exact pmv_range_congr _ _ _ _ (near_degree hn ht ha hR0 right power eta eps z hc hg)
    (fun j => congrArg RealIteratedTarski.lex
      (CoefficientMarkedRecordProperWordTuple.near_principal_eq hn ht ha hR0 right power eta eps z hc hg hlarge w hv raw hj j))

theorem rank_value_eq (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n true z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n true z)) (w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR0 true) z w)
    (raw : Fin (properPhysicalData hn ht ha true z).count → ℝ)
    (hj : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR0 true) z w hv).val raw) :
    rankStatistic hn ht ha hR0 power eps z w =
      permanencesMinusVariations ((List.range (max 1 (catalogDegree hn ht ha true z) + 1)).reverse.map
        (fun j => RealIteratedTarski.lex (CoefficientMarkedRecordProperPrincipalSeries.rank hn ht ha power eps z hc j
          ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n true z)) raw))) := by
  apply (rank_principals hn ht ha hR0 power eps z w hv).trans
  exact pmv_range_congr _ _ _ _ (rank_degree hn ht ha hR0 power eps z hc hg)
    (fun j => congrArg RealIteratedTarski.lex
      (CoefficientMarkedRecordProperWordTuple.rank_principal_eq hn ht ha hR0 power eps z hc hg hlarge w hv raw hj j))

end LeanCanny.Encoding.CoefficientMarkedRecordProperWordValue
