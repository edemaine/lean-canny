/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperNearRadiusHeight
/-! # Literal original padding metadata for the proper principal families -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters certifiedParameters certifiedPlan certifiedData)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def catalogPackedDegree (mean : Bool) (z : List Bool) :=
  let P := parameters hn ht ha
  let r := catalogRoot n mean z
  let m := catalogCreating n z
  (2^P.width r-1)+UniformIntegralPowerSchedule.birth (P.cap r+1) (2^P.width r) (m-1)*(m*(2^P.width r-1))

noncomputable def catalogNativeWidth (mean : Bool) (z : List Bool) :=
  (catalogPackedDegree hn ht ha mean z).size

noncomputable def catalogShiftDegree (mean : Bool) (z : List Bool) :=
  (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n mean z)+1)*
    2^catalogNativeWidth hn ht ha mean z

private theorem packed_degree_formula (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (parent : List Bool → List Bool) (e : List Bool → ℕ)
    (q : List Bool) :
    IntegralMixedFramedCoordinatePackedBits.degreeBound P D H parent e q =
      e q+UniformIntegralPowerSchedule.birth (P.cap (RankedHistoryTask.root (parent q))+1)
        (2^P.width (RankedHistoryTask.root (parent q))) (birth P (parent q)-1)*
        (birth P (parent q)*(2^P.width (RankedHistoryTask.root (parent q))-1)) := by
  simp only [IntegralMixedFramedCoordinatePackedBits.degreeBound,
    IntegralMixedFramedAllCoordinateSourceBits.degree, IntegralMixedFramedAllCoordinateSourceBits.horizon,
    IntegralMixedFramedAllCoordinateSourceBits.arity, IntegralMixedFramedAllCoordinateSourceBits.width]

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed

variable {R0 : List Bool → ℕ} (hR0 : BinaryFn R0)

theorem principal_parent_birth (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    birth (certifiedParameters hn ht ha (radius_binary hR0)) (parent hn ht ha hR0 mean z) =
      catalogCreating n z := by
  have HB := parent_birth hn ht ha hR0 mean z hc
  change birth (certifiedParameters hn ht ha (radius_binary hR0)) _ = _ at HB
  exact HB.trans (creating_catalog hn ht ha hR0 z)

theorem principal_terminal_count (mean : Bool) (z : List Bool) :
    (IntegralMixedFramedBankSnapshotBits.atKey (certifiedParameters hn ht ha (radius_binary hR0))
      (certifiedPlan hn ht ha (radius_binary hR0)) (certifiedData hn ht ha (radius_binary hR0))
      (terminal hn ht ha hR0 mean z)).count =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n mean z) := by
  rw [terminal_catalog]
  simpa only [IntegralMixedAuxiliaryMarkedRecordPlan.bankKey, pairFst_pair, catalogTerminal] using
    IntegralMixedAuxiliaryMarkedRecordPlan.bank_count hn ht ha (radius_binary hR0)
      (pair (catalogRoot n mean z) [])

theorem principal_packed_degree (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedFramedCoordinatePackedBits.degreeBound
      (certifiedParameters hn ht ha (radius_binary hR0)) (certifiedPlan hn ht ha (radius_binary hR0))
      (certifiedData hn ht ha (radius_binary hR0)) (parent hn ht ha hR0 mean)
      (IntegralMixedSelectedCoordinateHead.fullParameter (certifiedParameters hn ht ha (radius_binary hR0))
        (parent hn ht ha hR0 mean)) z = catalogPackedDegree hn ht ha mean z := by
  have HE : IntegralMixedSelectedCoordinateHead.fullParameter
      (certifiedParameters hn ht ha (radius_binary hR0)) (parent hn ht ha hR0 mean) z =
      2^(parameters hn ht ha).width (catalogRoot n mean z)-1 := by
    unfold IntegralMixedSelectedCoordinateHead.fullParameter
    rw [parent_root, root_catalog]
    rfl
  rw [packed_degree_formula, HE,
    principal_parent_birth hn ht ha hR0 mean z hc, parent_root, root_catalog]
  rfl

/-- This is the installed Kronecker width, rather than a replacement upper bound. -/
theorem principal_native_width (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedFramedCoordinateBivariateBits.nativeWidth
      (certifiedParameters hn ht ha (radius_binary hR0)) (certifiedPlan hn ht ha (radius_binary hR0))
      (certifiedData hn ht ha (radius_binary hR0)) (parent hn ht ha hR0 mean)
      (IntegralMixedSelectedCoordinateHead.fullParameter (certifiedParameters hn ht ha (radius_binary hR0))
        (parent hn ht ha hR0 mean)) z = catalogNativeWidth hn ht ha mean z := by
  exact congrArg Nat.size (principal_packed_degree hn ht ha hR0 mean z hc)

/-- The even clearing exponent is fixed by original structural bytes. -/
theorem principal_shift_degree (mean : Bool) (index : List Bool → ℕ) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    RationalMonomialParameterShift.sourceDegree
      (IntegralMixedFramedTerminalParameterShiftBits.endpointFamily
        (certifiedParameters hn ht ha (radius_binary hR0)) (certifiedPlan hn ht ha (radius_binary hR0))
        (certifiedData hn ht ha (radius_binary hR0)) (fun _ => 3)
        (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
        (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0))
        (terminal hn ht ha hR0 mean) index)
      (IntegralMixedFramedCoordinateBivariateBits.nativeWidth
        (certifiedParameters hn ht ha (radius_binary hR0)) (certifiedPlan hn ht ha (radius_binary hR0))
        (certifiedData hn ht ha (radius_binary hR0)) (parent hn ht ha hR0 mean)
        (IntegralMixedSelectedCoordinateHead.fullParameter (certifiedParameters hn ht ha (radius_binary hR0))
          (parent hn ht ha hR0 mean))) z = catalogShiftDegree hn ht ha mean z := by
  change ((IntegralMixedFramedBankSnapshotBits.atKey
    (certifiedParameters hn ht ha (radius_binary hR0)) (certifiedPlan hn ht ha (radius_binary hR0))
    (certifiedData hn ht ha (radius_binary hR0)) (terminal hn ht ha hR0 mean z)).count+1)*2^_ = _
  rw [principal_terminal_count hn ht ha hR0 mean z, principal_native_width hn ht ha hR0 mean z hc]
  rfl

noncomputable def catalogCenterIndex (right : Bool) (z : List Bool) :=
  IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n false z)-1-oldProducer right z

noncomputable def catalogPointProducer (mid : Bool) (z : List Bool) :=
  (if mid then IntegralMixedRoadmapProper.midFirst (catalogDimension n z) (catalogInitial n z) (atomic z)
    else IntegralMixedRoadmapAtomic.first (catalogDimension n z) (catalogInitial n z) (atomic z))+
      (catalogDimension n z-coordinate z)

noncomputable def catalogPointIndex (mean mid : Bool) (z : List Bool) :=
  IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n mean z)-1-catalogPointProducer (n := n) mid z

noncomputable def catalogWindowWeight (mean : Bool) (index : List Bool → ℕ) (z : List Bool) :=
  let P := parameters hn ht ha
  let r := catalogRoot n mean z
  let m := IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n r
  UniformIntegralPowerSchedule.birth (P.cap r+1) (2^P.width r) (m-1-min (index z) m)

private theorem weight_packet (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) (index : ℕ) :
    IntegralMixedFramedBankCoordinateBits.weight P D H (IntegralMixedFramedBankSnapshotBits.packet key [] index 0) =
      UniformIntegralPowerSchedule.birth (P.cap (pairFst key)+1) (2^P.width (pairFst key))
        ((IntegralMixedFramedBankSnapshotBits.atKey P D H key).count-1-
          min index (IntegralMixedFramedBankSnapshotBits.atKey P D H key).count) := by
  simp only [IntegralMixedFramedBankCoordinateBits.weight, UniformIntegralPowerSchedule.power,
    UniformIntegralPowerSchedule.age, IntegralMixedFramedBankCoordinateBits.horizon,
    IntegralMixedFramedBankCoordinateBits.scalarDegree, IntegralMixedFramedCompanionQueryBits.root,
    IntegralMixedFramedBankDenominatorBits.count, IntegralMixedFramedBankSnapshotBits.packet,
    IntegralMixedFramedBankSnapshotBits.atKey, PaddedIntegralGeneratorSource.base,
    PaddedIntegralGeneratorSource.row, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem principal_center_index (right : Bool) (z : List Bool) :
    centerIndex hn ht ha hR0 right z = catalogCenterIndex (n := n) right z := by
  unfold centerIndex catalogCenterIndex
  change (IntegralMixedFramedBankSnapshotBits.atKey
    (certifiedParameters hn ht ha (radius_binary hR0)) (certifiedPlan hn ht ha (radius_binary hR0))
    (certifiedData hn ht ha (radius_binary hR0)) _).count-1-_ = _
  rw [principal_terminal_count hn ht ha hR0 false z]

theorem principal_point_index (mean mid : Bool) (z : List Bool) :
    pointIndex hn ht ha hR0 mean mid z = catalogPointIndex (n := n) mean mid z := by
  have HP : pointProducer hn ht ha hR0 mid z = catalogPointProducer (n := n) mid z := by
    cases mid <;> simp only [pointProducer, catalogPointProducer, Bool.false_eq_true, ite_false, ite_true,
      dimension_catalog, initial_catalog, IntegralMixedRoadmapProper.childProducer, IntegralMixedRoadmapProper.midProducer]
  unfold pointIndex catalogPointIndex
  rw [HP]
  change (IntegralMixedFramedBankSnapshotBits.atKey
    (certifiedParameters hn ht ha (radius_binary hR0)) (certifiedPlan hn ht ha (radius_binary hR0))
    (certifiedData hn ht ha (radius_binary hR0)) _).count-1-_ = _
  rw [principal_terminal_count hn ht ha hR0 mean z]

theorem principal_window_weight (mean : Bool) (index : List Bool → ℕ) (z : List Bool) :
    (IntegralMixedFramedWindowQuery.family
      (certifiedParameters hn ht ha (radius_binary hR0)) (certifiedPlan hn ht ha (radius_binary hR0))
      (certifiedData hn ht ha (radius_binary hR0)) (fun _ => 3)
      (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0))
      (terminal hn ht ha hR0 mean) index).weight z = catalogWindowWeight hn ht ha mean index z := by
  change IntegralMixedFramedBankCoordinateBits.weight _ _ _
    (IntegralMixedFramedBankSnapshotBits.packet (terminal hn ht ha hR0 mean z) [] (index z) 0) = _
  rw [weight_packet, principal_terminal_count hn ht ha hR0 mean z, terminal_catalog]
  simp only [catalogTerminal, IntegralMixedFramedHistoryFamilyBits.keyAt, pairFst_pair]
  rfl

noncomputable def catalogPrincipalHeadBound (mean right : Bool) (z : List Bool) :=
  if mean then catalogPackedDegree hn ht ha true z else
    catalogShiftDegree hn ht ha false z*(catalogWindowWeight hn ht ha false (catalogCenterIndex (n := n) right) z+1)

noncomputable def catalogPrincipalQueryBound (mean : Bool) (z : List Bool) :=
  2*(catalogWindowWeight hn ht ha mean (catalogPointIndex (n := n) mean mean) z+1)

noncomputable def catalogPrincipalWidth (mean right : Bool) (z : List Bool) :=
  let d := max 1 (catalogDegree hn ht ha mean z)
  let hp := catalogPrincipalHeadBound hn ht ha mean right z
  let hq := catalogPrincipalQueryBound hn ht ha mean z
  (hp+hq+MultivariateTarskiDegreeBounds.principalDegreeBound d (d-1) (d+2) hp hq).size

theorem near_width_catalog (right : Bool) (power : Fin 3) (negativeEta negativeEpsilon : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z) :
    (nearFamily hn ht ha hR0 right power negativeEta negativeEpsilon).width z =
      catalogPrincipalWidth hn ht ha false right z := by
  have HC : centerIndex hn ht ha hR0 right = catalogCenterIndex (n := n) right :=
    funext (principal_center_index hn ht ha hR0 right)
  have HI : pointIndex hn ht ha hR0 false false = catalogPointIndex (n := n) false false :=
    funext (principal_point_index hn ht ha hR0 false false)
  have HD := near_degree_catalog_of_count hn ht ha hR0 z hc ((rank_row_good_iff hn ht ha hR0 z).mpr hg)
  dsimp only [nearFamily, IntegralFramedTerminalTarskiStatistic.mf,
    IntegralMixedFramedTerminalTarskiFamilyBits.family]
  unfold IntegralMixedFramedTerminalTarskiFamilyBits.width IntegralMixedFramedTerminalTarskiFamilyBits.wholeBound
    IntegralMixedFramedTerminalTarskiFamilyBits.principalBound IntegralMixedFramedTerminalTarskiFamilyBits.headBound
    IntegralMixedFramedTerminalTarskiFamilyBits.queryBound IntegralMixedFramedTerminalTarskiFamilyBits.windowBound
    IntegralMixedFramedTerminalTarskiFamilyBits.degree IntegralMixedFramedTerminalTarskiFamilyBits.seedDegree
    IntegralMixedFramedTerminalTarskiFamilyBits.inputBound IntegralMixedFramedTerminalTarskiHeadBits.degreeBound
  rw [principal_shift_degree hn ht ha hR0 false _ z hc]
  dsimp only [IntegralMixedFramedTerminalParameterShiftBits.endpointFamily]
  rw [principal_window_weight hn ht ha hR0 false _ z, principal_window_weight hn ht ha hR0 false _ z,
    HD, HC, HI]
  unfold catalogPrincipalWidth catalogPrincipalHeadBound catalogPrincipalQueryBound
  simp only [Bool.false_eq_true, ite_false, IntegralMixedFramedTerminalTarskiFamilyBits.degree, HD]

theorem rank_width_catalog (power : Fin 3) (negativeEpsilon : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z) :
    (rankFamily hn ht ha hR0 power negativeEpsilon).width z =
      catalogPrincipalWidth hn ht ha true false z := by
  have HI : pointIndex hn ht ha hR0 true true = catalogPointIndex (n := n) true true :=
    funext (principal_point_index hn ht ha hR0 true true)
  have HD := rank_degree_catalog_of_count hn ht ha hR0 z hc ((rank_row_good_iff hn ht ha hR0 z).mpr hg)
  dsimp only [rankFamily, IntegralFramedZeroTarskiStatistic.mf, IntegralMixedFramedZeroTarskiBits.family]
  unfold IntegralMixedFramedZeroTarskiBits.width IntegralMixedFramedZeroTarskiBits.wholeBound
    IntegralMixedFramedZeroTarskiBits.principalBound IntegralMixedFramedZeroTarskiBits.headBound
    IntegralMixedFramedZeroTarskiBits.queryBound IntegralMixedFramedZeroTarskiBits.windowBound
    IntegralMixedFramedZeroTarskiBits.degree IntegralMixedFramedZeroTarskiBits.seedDegree
    IntegralMixedFramedZeroTarskiBits.inputBound
  rw [principal_packed_degree hn ht ha hR0 true z hc, principal_window_weight hn ht ha hR0 true _ z, HD, HI]
  unfold catalogPrincipalWidth catalogPrincipalHeadBound catalogPrincipalQueryBound
  simp only [ite_true, IntegralMixedFramedZeroTarskiBits.degree, HD]

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
