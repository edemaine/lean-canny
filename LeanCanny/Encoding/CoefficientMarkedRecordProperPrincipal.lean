/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperWindow
public import LeanCanny.Algebra.CoefficientTarskiZeroParameterQueries
/-! # Constructed eta and eta-zero principal families of actual proper rows -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientTarskiParameterQueries
open Polynomial
variable {R S : Type*} [CommRing R] [CommRing S]

noncomputable def castHead {m k : ℕ} (h : m = k) (p : Polynomial (MvPolynomial (Fin m) R)) :
    Polynomial (MvPolynomial (Fin k) R) := p.map (MvPolynomial.rename (Fin.cast h)).toRingHom

theorem castHead_heq {m k : ℕ} (h : m = k) (p : Polynomial (MvPolynomial (Fin m) R)) :
    HEq (castHead h p) p := by
  cases h
  simp [castHead]

theorem castHead_map {m k : ℕ} (φ : R →+* S) (h : m = k) (p : Polynomial (MvPolynomial (Fin m) R)) :
    (castHead h p).map (MvPolynomial.map φ) = castHead h (p.map (MvPolynomial.map φ)) := by
  apply Polynomial.ext
  intro y
  simp only [castHead, Polynomial.coeff_map]
  change MvPolynomial.map φ (MvPolynomial.rename _ (p.coeff y)) =
    MvPolynomial.rename _ (MvPolynomial.map φ (p.coeff y))
  exact MvPolynomial.map_rename _ _ _

theorem shiftedHead_heq {m k : ℕ} (p : Polynomial (MvPolynomial (Fin (m+1)) ℤ))
    (p' : Polynomial (MvPolynomial (Fin (k+1)) ℤ)) (D D' : ℕ) (q a q' a' : ℤ)
    (index index' w w' : ℕ) (negative : Bool) (hm : m = k) (hp : HEq p p')
    (hD : D = D') (hq : q = q') (ha : a = a') (hi : index = index') (hw : w = w') :
    HEq (shiftedHead p D q a index w negative) (shiftedHead p' D' q' a' index' w' negative) := by
  cases hm
  cases hD
  cases hq
  cases ha
  cases hi
  cases hw
  cases eq_of_heq hp
  rfl

theorem pair_heq {m k : ℕ} (keep : Bool) (p : Polynomial (MvPolynomial (Fin (m+1)) ℤ))
    (p' : Polynomial (MvPolynomial (Fin (k+1)) ℤ)) (hm : m = k) (hp : HEq p p') :
    HEq (pairLift keep p) (pairLift keep p') := by
  cases hm
  cases eq_of_heq hp
  rfl

theorem zeroHead_heq {m k : ℕ} (p : Polynomial (MvPolynomial (Fin (m+1)) ℤ))
    (p' : Polynomial (MvPolynomial (Fin (k+1)) ℤ)) (hm : m = k) (hp : HEq p p') :
    HEq (CoefficientTarskiZeroParameterQueries.zeroHead p) (CoefficientTarskiZeroParameterQueries.zeroHead p') := by
  cases hm
  cases eq_of_heq hp
  rfl

theorem epsilonHead_heq {m k : ℕ} (p : Polynomial (MvPolynomial (Fin (m+1)) ℤ))
    (p' : Polynomial (MvPolynomial (Fin (k+1)) ℤ)) (hm : m = k) (hp : HEq p p') :
    HEq (CoefficientTarskiZeroParameterQueries.epsilonHead p) (CoefficientTarskiZeroParameterQueries.epsilonHead p') := by
  cases hm
  cases eq_of_heq hp
  rfl

theorem polynomial_pow_heq {m k : ℕ} (p : Polynomial (MvPolynomial (Fin m) ℤ))
    (p' : Polynomial (MvPolynomial (Fin k) ℤ)) (hm : m = k) (hp : HEq p p') (power : ℕ) :
    HEq (p^power) (p'^power) := by
  cases hm
  cases eq_of_heq hp
  rfl

theorem principal_heq {m k : ℕ} (p q : Polynomial (MvPolynomial (Fin m) ℤ))
    (p' q' : Polynomial (MvPolynomial (Fin k) ℤ)) (d d' s s' D D' j : ℕ)
    (hm : m = k) (hp : HEq p p') (hq : HEq q q') (hd : d = d') (hs : s = s') (hD : D = D') :
    HEq (principal p q d s D j) (principal p' q' d' s' D' j) := by
  cases hm
  cases eq_of_heq hp
  cases eq_of_heq hq
  cases hd
  cases hs
  cases hD
  rfl

theorem shift_native (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (parent terminal : List Bool → List Bool) (d e center : List Bool → ℕ) (negative : Bool) (z : List Bool) :
    shiftedHead (IntegralMixedFramedTerminalCoordinateHeadBits.polynomial P D H parent terminal d e z)
      (RationalMonomialParameterShift.sourceDegree
        (IntegralMixedFramedTerminalParameterShiftBits.endpointFamily P D H L F C hs terminal center)
        (IntegralMixedFramedCoordinateBivariateBits.nativeWidth P D H parent e) z)
      (IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal z)).common
      ((IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal z)).cofactor (center z)) (center z)
      ((IntegralMixedFramedWindowQuery.family P D H L F C hs terminal center).weight z) negative =
      IntegralMixedFramedTerminalTarskiHeadBits.head P D H L F C hs parent terminal d e center negative z := rfl

end LeanCanny.Algebra.CoefficientTarskiParameterQueries

namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR Polynomial
open CoefficientTarskiParameterQueries
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedRecordPlan (certifiedParameters certifiedPlan certifiedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

include hn ht ha in
theorem proper_terminal_cast_arity (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    1+(CoefficientMarkedRecordCutSource.birth (n := n) (catalogRoot n mean z) (catalogStage z)+1) =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n mean z)+1 := by
  rw [proper_symbolic_birth hn ht ha (BinaryFn.const 0) mean z hc,
    proper_full_count hn ht ha (BinaryFn.const 0) mean z hc]
  omega

noncomputable def properTerminalCast (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :=
  castHead (proper_terminal_cast_arity hn ht ha mean z hc) (properTerminalHead hn ht ha mean z)

noncomputable def properShiftedHead (right eta : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :=
  let center := catalogCenterIndex (n := n) right
  shiftedHead (properTerminalCast hn ht ha false z hc) (catalogShiftDegree hn ht ha false z)
    (properCommon hn ht ha false z) (properCofactor hn ht ha false center z) (center z)
    (catalogWindowWeight hn ht ha false center z) eta

noncomputable def properPointWindow (mean eps : Bool) (z : List Bool) :=
  properWindow hn ht ha mean (catalogPointIndex (n := n) mean mean) eps z

noncomputable def properNearHead (right eta : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) := pairLift true (properShiftedHead hn ht ha right eta z hc)
noncomputable def properNearQuery (power : Fin 3) (eps : Bool) (z : List Bool) :=
  pairLift false (properPointWindow hn ht ha false eps z)^power.val
noncomputable def properRankHead (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :=
  CoefficientTarskiZeroParameterQueries.zeroHead (properTerminalCast hn ht ha true z hc)
noncomputable def properRankQuery (power : Fin 3) (eps : Bool) (z : List Bool) :=
  CoefficientTarskiZeroParameterQueries.epsilonHead (properPointWindow hn ht ha true eps z)^power.val

noncomputable def properNearPrincipal (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (j : ℕ) :=
  let d := max 1 (catalogDegree hn ht ha false z)
  principal (properNearHead hn ht ha right eta z hc) (properNearQuery hn ht ha power eps z) d (d-1) (d+2) j

noncomputable def properRankPrincipal (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (j : ℕ) :=
  let d := max 1 (catalogDegree hn ht ha true z)
  principal (properRankHead hn ht ha z hc) (properRankQuery hn ht ha power eps z) d (d-1) (d+2) j

variable {R0 : List Bool → ℕ} (hR0 : BinaryFn R0)
local notation "PC" => certifiedParameters hn ht ha (radius_binary hR0)
local notation "DC" => certifiedPlan hn ht ha (radius_binary hR0)
local notation "HC" => certifiedData hn ht ha (radius_binary hR0)
local notation "dg" => IntegralMixedSelectedCoordinateHead.fullDegree PC
  (IntegralMixedFramedHistoryFamilyBits.family PC DC HC)
local notation "ep" => IntegralMixedSelectedCoordinateHead.fullParameter PC

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed

noncomputable def properNativeShift (right eta : Bool) (z : List Bool) :=
  let F := IntegralMixedFramedTerminalParameterShiftBits.endpointFamily PC DC HC (fun _ => 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0))
    (terminal hn ht ha hR0 false) (catalogCenterIndex (n := n) right)
  shiftedHead (IntegralMixedFramedTerminalCoordinateHeadBits.polynomial PC DC HC
    (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
    (dg (parent hn ht ha hR0 false)) (ep (parent hn ht ha hR0 false)) z)
    (RationalMonomialParameterShift.sourceDegree F
      (IntegralMixedFramedCoordinateBivariateBits.nativeWidth PC DC HC (parent hn ht ha hR0 false)
        (ep (parent hn ht ha hR0 false))) z)
    (IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (terminal hn ht ha hR0 false z)).common
    ((IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (terminal hn ht ha hR0 false z)).cofactor
      (catalogCenterIndex (n := n) right z)) (catalogCenterIndex (n := n) right z) (F.weight z) eta

theorem proper_terminal_cast_specializes (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n mean z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)) :
    HEq ((properTerminalCast hn ht ha mean z hc).map (MvPolynomial.map
      (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)))))
      (IntegralMixedFramedTerminalCoordinateHeadBits.polynomial PC DC HC
        (parent hn ht ha hR0 mean) (terminal hn ht ha hR0 mean)
        (dg (parent hn ht ha hR0 mean)) (ep (parent hn ht ha hR0 mean)) z) := by
  unfold properTerminalCast
  rw [castHead_map]
  exact (castHead_heq _ _).trans (proper_terminal_head_specializes hn ht ha hR0 mean z hc hg hR)

theorem proper_shifted_operator_specializes (right eta : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n false z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)) :
    HEq ((properShiftedHead hn ht ha right eta z hc).map (MvPolynomial.map
      (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)))))
      (properNativeShift hn ht ha hR0 right eta z) := by
  have HP := proper_terminal_cast_specializes hn ht ha hR0 false z hc hg hR
  obtain ⟨HQ, HA⟩ := proper_terminal_products hn ht ha hR0 false z (catalogCenterIndex (n := n) right) hR
  change (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)))
    (properCommon hn ht ha false z) = _ at HQ
  change (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)))
    (properCofactor hn ht ha false (catalogCenterIndex (n := n) right) z) = _ at HA
  have HCount := (principal_terminal_count hn ht ha hR0 false z).symm
  have HD := (principal_shift_degree hn ht ha hR0 false (catalogCenterIndex (n := n) right) z hc).symm
  have HW := (principal_window_weight hn ht ha hR0 false (catalogCenterIndex (n := n) right) z).symm
  unfold properShiftedHead
  rw [shiftedHead_map]
  have HM := shiftedHead_heq _ _ _ _ _ _ _ _ (catalogCenterIndex (n := n) right z)
    (catalogCenterIndex (n := n) right z) _ _ eta HCount HP HD HQ HA rfl HW
  unfold properNativeShift
  exact HM


theorem proper_shifted_head_specializes (right eta : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n false z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)) :
    HEq ((properShiftedHead hn ht ha right eta z hc).map (MvPolynomial.map
      (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)))))
      (IntegralMixedFramedTerminalTarskiHeadBits.head PC DC HC (fun _ => 3)
        (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
        (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0))
        (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
        (dg (parent hn ht ha hR0 false)) (ep (parent hn ht ha hR0 false))
        (catalogCenterIndex (n := n) right) eta z) := by
  have HM := proper_shifted_operator_specializes hn ht ha hR0 right eta z hc hg hR
  have HN := shift_native PC DC HC (fun _ => 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0))
    (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
    (dg (parent hn ht ha hR0 false)) (ep (parent hn ht ha hR0 false))
    (catalogCenterIndex (n := n) right) eta z
  unfold properNativeShift at HM
  exact HM.trans (heq_of_eq HN)

theorem proper_point_window_specializes (mean eps : Bool) (z : List Bool)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n mean z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)) :
    HEq ((properPointWindow hn ht ha mean eps z).map (MvPolynomial.map
      (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)))))
      (IntegralMixedFramedWindowQuery.polynomial PC DC HC (fun _ => 3)
        (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
        (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0))
        (terminal hn ht ha hR0 mean) (pointIndex hn ht ha hR0 mean mean) eps z) := by
  have HM := proper_window_specializes hn ht ha hR0 mean (catalogPointIndex (n := n) mean mean) eps z hR
  change HEq ((properPointWindow hn ht ha mean eps z).map _) _ at HM
  have HI := funext (principal_point_index hn ht ha hR0 mean mean)
  rw [← HI] at HM
  exact HM

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
