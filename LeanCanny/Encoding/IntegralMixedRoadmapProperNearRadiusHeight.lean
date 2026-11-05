/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRankRadiusHeight
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusShiftHead
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRankNative
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowStructuralCatalog
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusCertifiedWindow
/-! # Affine radius mass for the installed ordinary Near principals

The actual eta shift is retained. The epsilon window remains,
with its actual powers zero, one and two and both endpoint signs.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask Polynomial
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedRecordPlan (certifiedParameters certifiedPlan certifiedData)
open IntegralMixedAuxiliaryMarkedRecordRadiusHeight
  (rawSlope nativeHeadOffset coordinateSlope coordinateOffset shiftAllowance)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

include hn ht ha in
theorem near_catalogRoot_FP : catalogRoot n false ∈ FP :=
  mem_FP_of_eq (root_FP hn ht ha (BinaryFn.const 0) false)
    (root_catalog hn ht ha (BinaryFn.const 0) false)

theorem near_catalogDegree_binary : BinaryFn (catalogDegree hn ht ha false) := by
  have HD : UnaryFn (catalogDimension n) :=
    (hn.comp (mem_FP_comp atomic_FP IntegralMixedRoadmapAtomic.original_FP)).add (UnaryFn.const 3)
  exact PurePowerReductionBounds.dimension_binary ((HD.sub offset_unary).add (UnaryFn.const 1))
    ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).degree.comp (near_catalogRoot_FP hn ht ha))

noncomputable def nearDegree (z : List Bool) := max 1 (catalogDegree hn ht ha false z)
noncomputable def nearShiftAllowance (z : List Bool) :=
  shiftAllowance hn ht ha (pair (catalogRoot n false z) (catalogRoot n false z))
noncomputable def nearHeadSlope (z : List Bool) := rawSlope hn ht ha (catalogRoot n false z)+
  2*nearShiftAllowance hn ht ha z*coordinateSlope hn ht ha (catalogRoot n false z)
noncomputable def nearHeadOffset (z : List Bool) := nativeHeadOffset hn ht ha (catalogRoot n false z)+
  2*nearShiftAllowance hn ht ha z*(coordinateOffset hn ht ha (catalogRoot n false z)+1)
noncomputable def nearMassSlope (z : List Bool) :=
  FixedWidthTarskiMass.principalSlope (nearDegree hn ht ha z) (nearDegree hn ht ha z-1) (nearDegree hn ht ha z+2)
    (nearHeadSlope hn ht ha z) (4*coordinateSlope hn ht ha (catalogRoot n false z))
noncomputable def nearMassOffset (z : List Bool) :=
  FixedWidthTarskiMass.principalOffset (nearDegree hn ht ha z) (nearDegree hn ht ha z-1) (nearDegree hn ht ha z+2)
    (catalogDegree hn ht ha false z) 2 (nearHeadOffset hn ht ha z)
    (4*coordinateOffset hn ht ha (catalogRoot n false z)+4)

theorem nearDegree_binary : BinaryFn (nearDegree hn ht ha) :=
  (BinaryFn.ite ((BinaryFn.const 1).le (near_catalogDegree_binary hn ht ha))
    (near_catalogDegree_binary hn ht ha) (BinaryFn.const 1)).of_eq (fun _ => Nat.max_def.symm)

theorem nearShiftAllowance_binary : BinaryFn (nearShiftAllowance hn ht ha) :=
  (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.shiftAllowance_binary hn ht ha).comp
    (mem_FP_pair (near_catalogRoot_FP hn ht ha) (near_catalogRoot_FP hn ht ha))

theorem nearHeadSlope_binary : BinaryFn (nearHeadSlope hn ht ha) := by
  have HK : BinaryFn (fun z => rawSlope hn ht ha (catalogRoot n false z)) :=
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope_binary hn ht ha).comp (near_catalogRoot_FP hn ht ha)
  have HC : BinaryFn (fun z => coordinateSlope hn ht ha (catalogRoot n false z)) :=
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.coordinateSlope_binary hn ht ha).comp (near_catalogRoot_FP hn ht ha)
  exact HK.add (((BinaryFn.const 2).mul (nearShiftAllowance_binary hn ht ha)).mul HC)

theorem nearHeadOffset_binary : BinaryFn (nearHeadOffset hn ht ha) := by
  have HK : BinaryFn (fun z => nativeHeadOffset hn ht ha (catalogRoot n false z)) :=
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.nativeHeadOffset_binary hn ht ha).comp (near_catalogRoot_FP hn ht ha)
  have HC : BinaryFn (fun z => coordinateOffset hn ht ha (catalogRoot n false z)) :=
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.coordinateOffset_binary hn ht ha).comp (near_catalogRoot_FP hn ht ha)
  exact HK.add (((BinaryFn.const 2).mul (nearShiftAllowance_binary hn ht ha)).mul (HC.add (BinaryFn.const 1)))

theorem nearMassSlope_binary : BinaryFn (nearMassSlope hn ht ha) :=
  FixedWidthTarskiMass.principalSlope_binary (nearDegree_binary hn ht ha)
    ((nearDegree_binary hn ht ha).sub (BinaryFn.const 1)) ((nearDegree_binary hn ht ha).add (BinaryFn.const 2))
    (nearHeadSlope_binary hn ht ha)
    ((BinaryFn.const 4).mul
      ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.coordinateSlope_binary hn ht ha).comp (near_catalogRoot_FP hn ht ha)))

theorem nearMassOffset_binary : BinaryFn (nearMassOffset hn ht ha) :=
  FixedWidthTarskiMass.principalOffset_binary (nearDegree_binary hn ht ha)
    ((nearDegree_binary hn ht ha).sub (BinaryFn.const 1)) ((nearDegree_binary hn ht ha).add (BinaryFn.const 2))
    (near_catalogDegree_binary hn ht ha) (BinaryFn.const 2)
    (nearHeadOffset_binary hn ht ha)
    (((BinaryFn.const 4).mul
      ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.coordinateOffset_binary hn ht ha).comp (near_catalogRoot_FP hn ht ha))).add
        (BinaryFn.const 4))

variable {R0 : List Bool → ℕ} (hR0 : BinaryFn R0)

noncomputable def nearFamily (right : Bool) (power : Fin 3) (negativeEta negativeEpsilon : Bool) :=
  IntegralFramedTerminalTarskiStatistic.mf (certifiedParameters hn ht ha (radius_binary hR0))
    (certifiedPlan hn ht ha (radius_binary hR0)) (certifiedData hn ht ha (radius_binary hR0))
    (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0))
    (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false) (centerIndex hn ht ha hR0 right) (pointIndex hn ht ha hR0 false false) power negativeEta negativeEpsilon

theorem nearFamily_installed (right : Bool) (power : Fin 3) (negativeEta negativeEpsilon : Bool) :
    nearFamily hn ht ha hR0 right power negativeEta negativeEpsilon =
      IntegralFramedTerminalTarskiStatistic.mf
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).parameters
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).plan
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).data
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).nodes
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).factor
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).seed
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).bounds
        (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false) (centerIndex hn ht ha hR0 right) (pointIndex hn ht ha hR0 false false) power negativeEta negativeEpsilon := rfl

private theorem near_family_degree (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).spatial key).degree = P.degree (pairFst key) := by
  rw [IntegralMixedFramedHistoryFamilyBits.family_spatial]
  exact H.degree_eq key

private theorem near_family_ambient (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family P D H).ambient key = P.ambient (pairFst key) := rfl

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed IntegralMixedFramedHistoryFamilyBits.family

/-- The required degree identity needs syntactic count and row checks, not a sampler word. -/
theorem near_degree_catalog_of_count (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z))
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    IntegralMixedSelectedCoordinateHead.fullDegree (certifiedParameters hn ht ha (radius_binary hR0))
      (IntegralMixedFramedHistoryFamilyBits.family (certifiedParameters hn ht ha (radius_binary hR0))
        (certifiedPlan hn ht ha (radius_binary hR0)) (certifiedData hn ht ha (radius_binary hR0)))
      (parent hn ht ha hR0 false) z = catalogDegree hn ht ha false z := by
  have HO : ((IntegralMixedFramedHistoryFamilyBits.family
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).parameters
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).plan
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).data).rule
        (parentKey hn ht ha hR0 false z)).critical.offset.val = offset z := by
    rw [rule_at_parent hn ht ha hR0 false z hc hg]
    exact parentData_offset hn ht ha hR0 false z (parent_good hn ht ha hR0 false z hc hg)
  have HB : IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false =
      IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha (radius_binary hR0) := rfl
  have HO' : ((IntegralMixedFramedHistoryFamilyBits.family
      (certifiedParameters hn ht ha (radius_binary hR0)) (certifiedPlan hn ht ha (radius_binary hR0))
      (certifiedData hn ht ha (radius_binary hR0))).rule (parentKey hn ht ha hR0 false z)).critical.offset.val = offset z :=
    (congrArg (fun B : IntegralFramedBankQuery.Bank =>
      ((IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).rule
        (parentKey hn ht ha hR0 false z)).critical.offset.val) HB).symm.trans HO
  rw [IntegralMixedFramedCoordinatePackedSelected.fullDegree_eq]
  change PurePowerReductionBounds.dimension
    ((IntegralMixedFramedHistoryFamilyBits.family _ _ _).ambient (parentKey hn ht ha hR0 false z) -
      ((IntegralMixedFramedHistoryFamilyBits.family _ _ _).rule (parentKey hn ht ha hR0 false z)).critical.offset.val + 1)
    ((IntegralMixedFramedHistoryFamilyBits.family _ _ _).spatial (parentKey hn ht ha hR0 false z)).degree = _
  have HA := root_dimension hn ht ha hR0 false z
  simp only [HB, IntegralMixedAuxiliaryMarkedRecordPlan.bank] at HA
  rw [HO', near_family_degree, near_family_ambient, parentKey_root, HA, dimension_catalog, root_catalog]
  rfl

private theorem near_window_rebudget (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C L' F' C' : List Bool → ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hs' : IntegralMixedFramedStepHeight.FamilyInputs P D L' F' C')
    (terminal : List Bool → List Bool) (selected : List Bool → ℕ) (negative : Bool) (q : List Bool) :
    IntegralMixedFramedWindowQuery.polynomial P D H L F C hs terminal selected negative q =
      IntegralMixedFramedWindowQuery.polynomial P D H L' F' C' hs' terminal selected negative q := by
  unfold IntegralMixedFramedWindowQuery.polynomial RationalMonomialWindowQuery.query
    RationalMonomialWindowQuery.body RationalMonomialWindowQuery.epsilon RationalMonomialWindowQuery.raw
    IntegralMixedFramedWindowQuery.family IntegralMixedFramedBankScalars.scalars
  rfl

private theorem near_query_rebudget (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C L' F' C' : List Bool → ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hs' : IntegralMixedFramedStepHeight.FamilyInputs P D L' F' C')
    (terminal : List Bool → List Bool) (selected : List Bool → ℕ) (power : List Bool → Fin 3) (negative : Bool) :
    IntegralMixedFramedTerminalTarskiFamilyBits.query P D H L F C hs terminal selected power negative =
      IntegralMixedFramedTerminalTarskiFamilyBits.query P D H L' F' C' hs' terminal selected power negative := by
  have HE : IntegralMixedFramedWindowQuery.polynomial P D H L F C hs terminal selected negative =
      IntegralMixedFramedWindowQuery.polynomial P D H L' F' C' hs' terminal selected negative :=
    _root_.funext (near_window_rebudget P D H L F C L' F' C' hs hs' terminal selected negative)
  unfold IntegralMixedFramedTerminalTarskiFamilyBits.query IntegralMixedFramedTerminalTarskiFamilyBits.baseQuery
  rw [HE]

theorem near_principal_mass (right : Bool) (power : Fin 3) (negativeEta negativeEpsilon : Bool) (z : List Bool) (j : ℕ)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z) :
    MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial (nearFamily hn ht ha hR0 right power negativeEta negativeEpsilon) z j) ≤
      2^(nearMassSlope hn ht ha z*R0 (IntegralMixedAuxiliaryMarkedIntegerSource.original (catalogRoot n false z))+
        nearMassOffset hn ht ha z) := by
  have HG := (rank_row_good_iff hn ht ha hR0 z).mpr hg
  let P := certifiedParameters hn ht ha (radius_binary hR0)
  let D := certifiedPlan hn ht ha (radius_binary hR0)
  let H := certifiedData hn ht ha (radius_binary hR0)
  let d := IntegralMixedSelectedCoordinateHead.fullDegree P (IntegralMixedFramedHistoryFamilyBits.family P D H)
    (parent hn ht ha hR0 false)
  let e := IntegralMixedSelectedCoordinateHead.fullParameter P (parent hn ht ha hR0 false)
  let F := nearFamily hn ht ha hR0 right power negativeEta negativeEpsilon
  let root := catalogRoot n false z
  let r := IntegralMixedOriginalRegularSource.radius R0 root
  let Kp := nearHeadSlope hn ht ha z
  let Hp := nearHeadOffset hn ht ha z
  let Kq := 4*coordinateSlope hn ht ha root
  let Hq := 4*coordinateOffset hn ht ha root+4
  have HD : (F.head z).natDegree ≤ d z :=
    IntegralMixedFramedTerminalTarskiFamilyBits.head_outer_degree P D H
      (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0))
      (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false) d e (centerIndex hn ht ha hR0 right) negativeEta z
  have HQ : (F.query z).natDegree ≤ 2 :=
    IntegralMixedFramedTerminalTarskiFamilyBits.query_outer_degree P D H
      (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0))
      (terminal hn ht ha hR0 false) (pointIndex hn ht ha hR0 false false) (fun _ => power) negativeEpsilon z
  have HR : pairFst (catalogTerminal n false z) = root := by
    simp only [catalogTerminal, IntegralMixedFramedHistoryFamilyBits.keyAt, pairFst_pair, root]
  have HP : ∀ i, MvMass.mass ((F.head z).coeff i) ≤ 2^(Kp*r+Hp) := by
    intro i
    have HM := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_shifted_head_mass hn ht ha (radius_binary hR0)
      (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false) d (centerIndex hn ht ha hR0 right) negativeEta z i
    have Hlift := FixedWidthBivariateParameterPairBits.mass true
      (IntegralMixedFramedTerminalTarskiFamilyBits.arity P D H (terminal hn ht ha hR0 false))
      (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.shiftedHead hn ht ha (radius_binary hR0)
        (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false) d (centerIndex hn ht ha hR0 right) negativeEta) z i
    have HH := Hlift.trans HM
    rw [parent_root, root_catalog, terminal_catalog, HR] at HH
    apply HH.trans (Nat.pow_le_pow_right (by decide) ?_)
    exact le_of_eq (by dsimp only [Kp, Hp, nearHeadSlope, nearHeadOffset, nearShiftAllowance, root]; ring)
  have HQQ : ∀ i, MvMass.mass ((F.query z).coeff i) ≤ 2^(Kq*r+Hq) := by
    intro i
    let hA := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_affine_inputs hn ht ha (radius_binary hR0)
    have HM := IntegralMixedFramedTerminalTarskiFamilyBits.query_coefficient_mass P D H
      (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.seed hn ht ha (IntegralMixedOriginalRegularSource.radius R0)) hA
      (terminal hn ht ha hR0 false) (pointIndex hn ht ha hR0 false false) (fun _ => power) negativeEpsilon z i
    have HC := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_coordinate_mass_affine hn ht ha (radius_binary hR0)
      (terminal hn ht ha hR0 false z)
    have HX : IntegralMixedFramedTerminalTarskiFamilyBits.queryHeight P D H
        (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.seed hn ht ha (IntegralMixedOriginalRegularSource.radius R0))
        (terminal hn ht ha hR0 false) z ≤
        (4*coordinateSlope hn ht ha (pairFst (terminal hn ht ha hR0 false z)))*
          IntegralMixedOriginalRegularSource.radius R0 (pairFst (terminal hn ht ha hR0 false z))+
        (4*coordinateOffset hn ht ha (pairFst (terminal hn ht ha hR0 false z))+4) := by
      unfold IntegralMixedFramedTerminalTarskiFamilyBits.queryHeight
      nlinarith only [HC]
    have HB := HM.trans (Nat.pow_le_pow_right (by decide) HX)
    rw [terminal_catalog, HR] at HB
    have HE := congrArg (fun f => MvMass.mass ((f z).coeff i))
      (near_query_rebudget P D H (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
        (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
        (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.seed hn ht ha (IntegralMixedOriginalRegularSource.radius R0))
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0)) hA
        (terminal hn ht ha hR0 false) (pointIndex hn ht ha hR0 false false) (fun _ => power) negativeEpsilon)
    exact HE.le.trans HB
  have HM := FixedWidthTarskiMass.principal_mass_direct F z j (d z) 2 (Kp*r+Hp) (Kq*r+Hq) HD HQ HP HQQ
  have HE : d z = catalogDegree hn ht ha false z := near_degree_catalog_of_count hn ht ha hR0 z hc HG
  change _ ≤ 2^FixedWidthTarskiMass.principalMass (max 1 (d z)) (max 1 (d z)-1) (max 1 (d z)+2)
    (d z) 2 (Kp*r+Hp) (Kq*r+Hq) at HM
  rw [HE] at HM
  exact HM.trans (Nat.pow_le_pow_right (by decide)
    (FixedWidthTarskiMass.principalMass_affine _ _ _ _ _ _ _ _ _ _))

theorem near_dimensions (right : Bool) (power : Fin 3) (negativeEta negativeEpsilon : Bool) (z : List Bool) :
    (nearFamily hn ht ha hR0 right power negativeEta negativeEpsilon).arity z =
      (IntegralMixedFramedBankSnapshotBits.atKey (certifiedParameters hn ht ha (radius_binary hR0))
        (certifiedPlan hn ht ha (radius_binary hR0)) (certifiedData hn ht ha (radius_binary hR0))
        (terminal hn ht ha hR0 false z)).count+2 := by
  change 1+((IntegralMixedFramedBankSnapshotBits.atKey
    (certifiedParameters hn ht ha (radius_binary hR0)) (certifiedPlan hn ht ha (radius_binary hR0))
    (certifiedData hn ht ha (radius_binary hR0)) (terminal hn ht ha hR0 false z)).count+1)=_
  omega

/-- Eta is axis zero, epsilon axis one; extraction precedes own scalar-column embedding. -/
noncomputable def nearPhysicalPrincipal (right : Bool) (power : Fin 3) (negativeEta negativeEpsilon : Bool)
    (z : List Bool) (j delta epsilon : ℕ) :
    MvPolynomial (Fin (IntegralFramedPhysicalSquare.count (certifiedParameters hn ht ha (radius_binary hR0))
      (certifiedPlan hn ht ha (radius_binary hR0)) (terminal hn ht ha hR0 false z))) ℤ :=
  let p := MvTwoParameterEncodedCoefficient.castPolynomial (near_dimensions hn ht ha hR0 right power negativeEta negativeEpsilon z)
    (FixedWidthTarskiPrincipalBits.polynomial (nearFamily hn ht ha hR0 right power negativeEta negativeEpsilon) z j)
  MvPolynomial.rename (IntegralMixedFramedScalarEmbedding.scalarMap
    (certifiedParameters hn ht ha (radius_binary hR0)) (certifiedPlan hn ht ha (radius_binary hR0))
    (certifiedData hn ht ha (radius_binary hR0)) (terminal hn ht ha hR0 false z))
    (MvTwoParameterCoefficient.slice p delta epsilon)

theorem near_physical_principal_mass (right : Bool) (power : Fin 3) (negativeEta negativeEpsilon : Bool)
    (z : List Bool) (j delta epsilon : ℕ)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z) :
    MvMass.mass (nearPhysicalPrincipal hn ht ha hR0 right power negativeEta negativeEpsilon z j delta epsilon) ≤
      2^(nearMassSlope hn ht ha z*R0 (IntegralMixedAuxiliaryMarkedIntegerSource.original (catalogRoot n false z))+
        nearMassOffset hn ht ha z) := by
  exact (MvMass.rename_le _ _).trans ((MvTwoParameterCoefficient.mass _ _ _).trans
    ((MvTwoParameterEncodedCoefficient.cast_mass _ _).trans
      (near_principal_mass hn ht ha hR0 right power negativeEta negativeEpsilon z j hc hg)))

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
