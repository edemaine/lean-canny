/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperHead
public import LeanCanny.Algebra.CoefficientTarskiParameterQueries
/-! # Literal one-scalar suffix of the actual proper coordinate head -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientTarskiParameterQueries
open Polynomial
theorem pairLift_heq {m k : ℕ} (p : Polynomial (MvPolynomial (Fin (m+1)) ℤ))
    (q : Polynomial (MvPolynomial (Fin (k+1)) ℤ)) (hm : m = k) (hp : HEq p q) :
    HEq (pairLift true p) (pairLift true q) := by
  cases hm
  cases eq_of_heq hp
  rfl
end LeanCanny.Algebra.CoefficientTarskiParameterQueries

namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedRecordPlan (certifiedParameters certifiedPlan certifiedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R0 : List Bool → ℕ} (hR0 : BinaryFn R0)
local notation "PC" => certifiedParameters hn ht ha (radius_binary hR0)
local notation "DC" => certifiedPlan hn ht ha (radius_binary hR0)
local notation "HC" => certifiedData hn ht ha (radius_binary hR0)
local notation "dg" => IntegralMixedSelectedCoordinateHead.fullDegree PC
  (IntegralMixedFramedHistoryFamilyBits.family PC DC HC)
local notation "ep" => IntegralMixedSelectedCoordinateHead.fullParameter PC

include hn ht ha hR0 in
theorem proper_symbolic_birth (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    CoefficientMarkedRecordCutSource.birth (n := n) (catalogRoot n mean z) (catalogStage z) = catalogCreating n z := by
  rw [CoefficientMarkedRecordCutSource.birth, CoefficientMarkedRecordActual.codes_length,
    CoefficientMarkedPreludeActual.indices_length]
  have HN := root_number hn ht ha hR0 mean z
  rw [root_catalog, initial_catalog] at HN
  rw [HN]
  unfold catalogStage catalogCreating IntegralMixedRoadmapBadProbePacket.creating
  omega

include hn ht ha hR0 in
theorem proper_full_count (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n mean z) = catalogCreating n z+1 := by
  have HCount := root_count hn ht ha hR0 mean z hc
  have HN := root_number hn ht ha hR0 mean z
  rw [root_catalog] at HCount
  rw [root_catalog, initial_catalog] at HN
  unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
  rw [HCount, HN]
  unfold catalogCreating IntegralMixedRoadmapBadProbePacket.creating
  omega

theorem proper_parent_arity (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedFramedCoordinateCoefficientSpaceBits.arity PC DC HC (parent hn ht ha hR0 mean) z = catalogCreating n z :=
  ((IntegralMixedFramedHistoryFamilyBits.geometry PC DC HC).birth (parent hn ht ha hR0 mean z)).trans
    (principal_parent_birth hn ht ha hR0 mean z hc)

theorem proper_parent_core (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z) :
    IntegralMixedFramedCoordinateCoefficientSpaceBits.Core PC (parent hn ht ha hR0 mean) z := by
  have HG := (rank_row_good_iff hn ht ha hR0 z).mpr hg
  have HX := parent_context hn ht ha hR0 mean z
  change get PC .slot15 (parent hn ht ha hR0 mean z) = 2 at HX
  constructor
  · constructor
    · unfold IntegralMixedVirtualCaps.valid
      rw [principal_parent_birth hn ht ha hR0 mean z hc, parent_root, root_catalog]
      change catalogCreating n z < IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n mean z)+2
      rw [proper_full_count hn ht ha hR0 mean z hc]
      omega
    · change 2 ≤ get PC .slot15 (parent hn ht ha hR0 mean z) ∧ get PC .slot15 (parent hn ht ha hR0 mean z) ≤ 4
      rw [HX]
      omega
  · have HJ := parent_coordinate hn ht ha hR0 mean z HG
    have HD := root_dimension hn ht ha hR0 mean z
    change get PC .slot13 (parent hn ht ha hR0 mean z) = relativeCoordinate z at HJ
    change (PC).ambient (root hn ht ha hR0 mean z) = dimension hn ht ha hR0 z at HD
    rw [HJ, parent_root, HD]
    exact (Nat.sub_le (coordinate z) (offset z)).trans (Nat.le_of_lt HG.1.2.2.2.2)

theorem proper_newer (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedFramedCoordinateParameterSuffixBits.newer PC DC HC
      (parent hn ht ha hR0 mean) (terminal hn ht ha hR0 mean) z = 1 := by
  unfold IntegralMixedFramedCoordinateParameterSuffixBits.newer
  rw [principal_terminal_count hn ht ha hR0 mean z, proper_parent_arity hn ht ha hR0 mean z hc,
    proper_full_count hn ht ha hR0 mean z hc]
  omega

theorem proper_terminal_valid (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedFramedTerminalCoordinateHeadBits.Valid PC DC HC
      (parent hn ht ha hR0 mean) (terminal hn ht ha hR0 mean) z := by
  unfold IntegralMixedFramedTerminalCoordinateHeadBits.Valid
  rw [principal_terminal_count hn ht ha hR0 mean z, proper_parent_arity hn ht ha hR0 mean z hc,
    proper_full_count hn ht ha hR0 mean z hc]
  omega

theorem proper_terminal_pair (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z) :
    HEq (IntegralMixedFramedTerminalCoordinateHeadBits.polynomial PC DC HC
      (parent hn ht ha hR0 mean) (terminal hn ht ha hR0 mean)
      (dg (parent hn ht ha hR0 mean)) (ep (parent hn ht ha hR0 mean)) z)
      (CoefficientTarskiParameterQueries.pairLift true (IntegralMixedFramedCoordinatePackedBits.head PC DC HC
        (parent hn ht ha hR0 mean) (dg (parent hn ht ha hR0 mean)) (ep (parent hn ht ha hR0 mean)) z)) := by
  have HP := IntegralMixedFramedTerminalCoordinateHeadBits.polynomial_heq PC DC HC
    (parent hn ht ha hR0 mean) (terminal hn ht ha hR0 mean)
    (dg (parent hn ht ha hR0 mean)) (ep (parent hn ht ha hR0 mean)) z
    (proper_terminal_valid hn ht ha hR0 mean z hc)
  have HQ : HEq (IntegralMixedFramedCoordinateParameterSuffixBits.polynomial PC DC HC
      (parent hn ht ha hR0 mean) (terminal hn ht ha hR0 mean)
      (dg (parent hn ht ha hR0 mean)) (ep (parent hn ht ha hR0 mean)) z)
      (CoefficientTarskiParameterQueries.pairLift true (IntegralMixedFramedCoordinatePackedBits.head PC DC HC
        (parent hn ht ha hR0 mean) (dg (parent hn ht ha hR0 mean)) (ep (parent hn ht ha hR0 mean)) z)) := by
    unfold IntegralMixedFramedCoordinateParameterSuffixBits.polynomial FixedWidthBivariateParameterSuffixBits.head
    rw [proper_newer hn ht ha hR0 mean z hc]
    rw [IntegralMixedFramedCoordinatePackedBits.guardedHead, ite_eq_left (proper_parent_core hn ht ha hR0 mean z hc hg)]
    rfl
  exact HP.trans HQ

noncomputable def properTerminalHead (mean : Bool) (z : List Bool) :=
  CoefficientTarskiParameterQueries.pairLift true (properHead hn ht ha mean z)

theorem proper_terminal_head_specializes (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n mean z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)) :
    HEq ((properTerminalHead hn ht ha mean z).map (MvPolynomial.map
      (Polynomial.evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)))))
      (IntegralMixedFramedTerminalCoordinateHeadBits.polynomial PC DC HC
        (parent hn ht ha hR0 mean) (terminal hn ht ha hR0 mean)
        (dg (parent hn ht ha hR0 mean)) (ep (parent hn ht ha hR0 mean)) z) := by
  unfold properTerminalHead
  rw [CoefficientTarskiParameterQueries.pairLift_map]
  have HA := (proper_symbolic_birth hn ht ha hR0 mean z hc).trans (proper_parent_arity hn ht ha hR0 mean z hc).symm
  have HM := CoefficientTarskiParameterQueries.pairLift_heq _ _ HA (proper_head_specializes hn ht ha hR0 mean z hc hg hR)
  exact HM.trans (proper_terminal_pair hn ht ha hR0 mean z hc hg).symm

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
