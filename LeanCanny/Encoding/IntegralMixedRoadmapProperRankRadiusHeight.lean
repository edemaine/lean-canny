/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthTarskiAffineMass
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRankNative
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowStructuralCatalog
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusCertifiedWindow
/-! # Affine radius mass for the installed mean-coordinate rank principals

Eta is specialized to zero in the actual head. The epsilon window remains,
with its actual powers zero, one and two and both endpoint signs.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask Polynomial
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedRecordPlan (certifiedParameters certifiedPlan certifiedData)
open IntegralMixedAuxiliaryMarkedRecordRadiusHeight
  (rawSlope nativeHeadOffset coordinateSlope coordinateOffset)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

include hn ht ha in
theorem rank_catalogRoot_FP : catalogRoot n true ∈ FP :=
  mem_FP_of_eq (root_FP hn ht ha (BinaryFn.const 0) true)
    (root_catalog hn ht ha (BinaryFn.const 0) true)

theorem rank_catalogDegree_binary : BinaryFn (catalogDegree hn ht ha true) := by
  have HD : UnaryFn (catalogDimension n) :=
    (hn.comp (mem_FP_comp atomic_FP IntegralMixedRoadmapAtomic.original_FP)).add (UnaryFn.const 3)
  exact PurePowerReductionBounds.dimension_binary ((HD.sub offset_unary).add (UnaryFn.const 1))
    ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).degree.comp (rank_catalogRoot_FP hn ht ha))

noncomputable def rankDegree (z : List Bool) := max 1 (catalogDegree hn ht ha true z)
noncomputable def rankMassSlope (z : List Bool) :=
  FixedWidthTarskiMass.principalSlope (rankDegree hn ht ha z) (rankDegree hn ht ha z-1) (rankDegree hn ht ha z+2)
    (rawSlope hn ht ha (catalogRoot n true z)) (4*coordinateSlope hn ht ha (catalogRoot n true z))
noncomputable def rankMassOffset (z : List Bool) :=
  FixedWidthTarskiMass.principalOffset (rankDegree hn ht ha z) (rankDegree hn ht ha z-1) (rankDegree hn ht ha z+2)
    (catalogDegree hn ht ha true z) 2 (nativeHeadOffset hn ht ha (catalogRoot n true z))
    (4*coordinateOffset hn ht ha (catalogRoot n true z)+4)

theorem rankDegree_binary : BinaryFn (rankDegree hn ht ha) :=
  (BinaryFn.ite ((BinaryFn.const 1).le (rank_catalogDegree_binary hn ht ha))
    (rank_catalogDegree_binary hn ht ha) (BinaryFn.const 1)).of_eq (fun _ => Nat.max_def.symm)

theorem rankMassSlope_binary : BinaryFn (rankMassSlope hn ht ha) :=
  FixedWidthTarskiMass.principalSlope_binary (rankDegree_binary hn ht ha)
    ((rankDegree_binary hn ht ha).sub (BinaryFn.const 1)) ((rankDegree_binary hn ht ha).add (BinaryFn.const 2))
    ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope_binary hn ht ha).comp (rank_catalogRoot_FP hn ht ha))
    ((BinaryFn.const 4).mul
      ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.coordinateSlope_binary hn ht ha).comp (rank_catalogRoot_FP hn ht ha)))

theorem rankMassOffset_binary : BinaryFn (rankMassOffset hn ht ha) :=
  FixedWidthTarskiMass.principalOffset_binary (rankDegree_binary hn ht ha)
    ((rankDegree_binary hn ht ha).sub (BinaryFn.const 1)) ((rankDegree_binary hn ht ha).add (BinaryFn.const 2))
    (rank_catalogDegree_binary hn ht ha) (BinaryFn.const 2)
    ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.nativeHeadOffset_binary hn ht ha).comp (rank_catalogRoot_FP hn ht ha))
    (((BinaryFn.const 4).mul
      ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.coordinateOffset_binary hn ht ha).comp (rank_catalogRoot_FP hn ht ha))).add
        (BinaryFn.const 4))

variable {R0 : List Bool → ℕ} (hR0 : BinaryFn R0)

noncomputable def rankFamily (power : Fin 3) (negative : Bool) :=
  IntegralFramedZeroTarskiStatistic.mf (certifiedParameters hn ht ha (radius_binary hR0))
    (certifiedPlan hn ht ha (radius_binary hR0)) (certifiedData hn ht ha (radius_binary hR0))
    (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0))
    (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true) (pointIndex hn ht ha hR0 true true) power negative

theorem rankFamily_installed (power : Fin 3) (negative : Bool) :
    rankFamily hn ht ha hR0 power negative =
      IntegralFramedZeroTarskiStatistic.mf
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).parameters
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).plan
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).data
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).nodes
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).factor
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).seed
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).bounds
        (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true) (pointIndex hn ht ha hR0 true true) power negative := rfl

private theorem family_degree (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).spatial key).degree = P.degree (pairFst key) := by
  rw [IntegralMixedFramedHistoryFamilyBits.family_spatial]
  exact H.degree_eq key

private theorem family_ambient (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family P D H).ambient key = P.ambient (pairFst key) := rfl

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed IntegralMixedFramedHistoryFamilyBits.family

/-- The required degree identity needs syntactic count and row checks, not a sampler word. -/
theorem rank_degree_catalog_of_count (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z))
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    IntegralMixedSelectedCoordinateHead.fullDegree (certifiedParameters hn ht ha (radius_binary hR0))
      (IntegralMixedFramedHistoryFamilyBits.family (certifiedParameters hn ht ha (radius_binary hR0))
        (certifiedPlan hn ht ha (radius_binary hR0)) (certifiedData hn ht ha (radius_binary hR0)))
      (parent hn ht ha hR0 true) z = catalogDegree hn ht ha true z := by
  have HO : ((IntegralMixedFramedHistoryFamilyBits.family
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).parameters
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).plan
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).data).rule
        (parentKey hn ht ha hR0 true z)).critical.offset.val = offset z := by
    rw [rule_at_parent hn ht ha hR0 true z hc hg]
    exact parentData_offset hn ht ha hR0 true z (parent_good hn ht ha hR0 true z hc hg)
  have HB : IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false =
      IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha (radius_binary hR0) := rfl
  have HO' : ((IntegralMixedFramedHistoryFamilyBits.family
      (certifiedParameters hn ht ha (radius_binary hR0)) (certifiedPlan hn ht ha (radius_binary hR0))
      (certifiedData hn ht ha (radius_binary hR0))).rule (parentKey hn ht ha hR0 true z)).critical.offset.val = offset z :=
    (congrArg (fun B : IntegralFramedBankQuery.Bank =>
      ((IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).rule
        (parentKey hn ht ha hR0 true z)).critical.offset.val) HB).symm.trans HO
  rw [IntegralMixedFramedCoordinatePackedSelected.fullDegree_eq]
  change PurePowerReductionBounds.dimension
    ((IntegralMixedFramedHistoryFamilyBits.family _ _ _).ambient (parentKey hn ht ha hR0 true z) -
      ((IntegralMixedFramedHistoryFamilyBits.family _ _ _).rule (parentKey hn ht ha hR0 true z)).critical.offset.val + 1)
    ((IntegralMixedFramedHistoryFamilyBits.family _ _ _).spatial (parentKey hn ht ha hR0 true z)).degree = _
  have HA := root_dimension hn ht ha hR0 true z
  simp only [HB, IntegralMixedAuxiliaryMarkedRecordPlan.bank] at HA
  rw [HO', family_degree, family_ambient, parentKey_root, HA, dimension_catalog, root_catalog]
  rfl

/-- Exactly the native row checks, expressed without a radius reader. -/
def rankRowSyntax (n : List Bool → ℕ) (z : List Bool) : Prop :=
  IntegralMixedChronologicalCutCode.Good (catalogDimension n z) (catalogCreating n z) (labels z) (offset z) (coordinate z) ∧
  IntegralMixedChronologicalMidpointCode.Good (catalogDimension n z) (catalogCreating n z) (labels z)
    (oldProducer false z) (oldProducer true z) (offset z) (coordinate z)

theorem rank_row_good_iff (z : List Bool) :
    IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z ↔ rankRowSyntax n z := by
  unfold IntegralMixedRoadmapProperRowWitness.RowGood rankRowSyntax
  rw [dimension_catalog, creating_catalog]

theorem rank_principal_mass (power : Fin 3) (negative : Bool) (z : List Bool) (j : ℕ)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z))
    (hg : rankRowSyntax n z) :
    MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial (rankFamily hn ht ha hR0 power negative) z j) ≤
      2^(rankMassSlope hn ht ha z * R0 (IntegralMixedAuxiliaryMarkedIntegerSource.original (catalogRoot n true z)) +
        rankMassOffset hn ht ha z) := by
  have HG : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z :=
    (rank_row_good_iff hn ht ha hR0 z).mpr hg
  let P := certifiedParameters hn ht ha (radius_binary hR0)
  let D := certifiedPlan hn ht ha (radius_binary hR0)
  let H := certifiedData hn ht ha (radius_binary hR0)
  let d := IntegralMixedSelectedCoordinateHead.fullDegree P (IntegralMixedFramedHistoryFamilyBits.family P D H)
    (parent hn ht ha hR0 true)
  let e := IntegralMixedSelectedCoordinateHead.fullParameter P (parent hn ht ha hR0 true)
  let F := rankFamily hn ht ha hR0 power negative
  let root := catalogRoot n true z
  let r := IntegralMixedOriginalRegularSource.radius R0 root
  let Kp := rawSlope hn ht ha root
  let Hp := nativeHeadOffset hn ht ha root
  let Kq := 4*coordinateSlope hn ht ha root
  let Hq := 4*coordinateOffset hn ht ha root+4
  have HD : (F.head z).natDegree ≤ d z :=
    IntegralMixedFramedZeroTarskiBits.head_outer_degree P D H _ _ d e z
  have HQ : (F.query z).natDegree ≤ 2 :=
    IntegralMixedFramedZeroTarskiBits.query_outer_degree P D H
      (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0))
      (terminal hn ht ha hR0 true) (pointIndex hn ht ha hR0 true true) (fun _ => power) negative z
  have HP : ∀ i, MvMass.mass ((F.head z).coeff i) ≤ 2^(Kp*r+Hp) := by
    intro i
    have HM := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_native_head_mass hn ht ha (radius_binary hR0)
      (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true) d z i
    rw [parent_root, root_catalog] at HM
    exact HM
  have HQQ : ∀ i, MvMass.mass ((F.query z).coeff i) ≤ 2^(Kq*r+Hq) := by
    intro i
    have HM := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_powered_window_coefficient_mass hn ht ha (radius_binary hR0)
      (terminal hn ht ha hR0 true) (pointIndex hn ht ha hR0 true true) (fun _ => power) negative z i
    rw [terminal_catalog] at HM
    have HR : pairFst (catalogTerminal n true z) = catalogRoot n true z := by
      simp only [catalogTerminal, IntegralMixedFramedHistoryFamilyBits.keyAt, pairFst_pair]
    rw [HR] at HM
    exact HM
  have HM := FixedWidthTarskiMass.principal_mass_direct F z j (d z) 2 (Kp*r+Hp) (Kq*r+Hq) HD HQ HP HQQ
  have HE : d z = catalogDegree hn ht ha true z := rank_degree_catalog_of_count hn ht ha hR0 z hc HG
  change _ ≤ 2^FixedWidthTarskiMass.principalMass (max 1 (d z)) (max 1 (d z)-1) (max 1 (d z)+2)
    (d z) 2 (Kp*r+Hp) (Kq*r+Hq) at HM
  rw [HE] at HM
  apply HM.trans
  apply Nat.pow_le_pow_right (by decide)
  exact FixedWidthTarskiMass.principalMass_affine _ _ _ _ _ _ _ _ _ _

/-- Extract delta/epsilon first, then use the actual full sampler's scalar slots. -/
noncomputable def rankPhysicalPrincipal (power : Fin 3) (negative : Bool) (z : List Bool) (j delta epsilon : ℕ) :
    MvPolynomial (Fin (IntegralFramedPhysicalSquare.count (certifiedParameters hn ht ha (radius_binary hR0))
      (certifiedPlan hn ht ha (radius_binary hR0)) (terminal hn ht ha hR0 true z))) ℤ :=
  let P := certifiedParameters hn ht ha (radius_binary hR0)
  let D := certifiedPlan hn ht ha (radius_binary hR0)
  let H := certifiedData hn ht ha (radius_binary hR0)
  let p := FixedWidthTarskiPrincipalBits.polynomial (rankFamily hn ht ha hR0 power negative) z j
  MvPolynomial.rename (IntegralMixedFramedScalarEmbedding.scalarMap P D H (terminal hn ht ha hR0 true z))
    (MvTwoParameterCoefficient.slice p delta epsilon)

theorem rank_physical_principal_mass (power : Fin 3) (negative : Bool) (z : List Bool) (j delta epsilon : ℕ)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z) :
    MvMass.mass (rankPhysicalPrincipal hn ht ha hR0 power negative z j delta epsilon) ≤
      2^(rankMassSlope hn ht ha z * R0 (IntegralMixedAuxiliaryMarkedIntegerSource.original (catalogRoot n true z)) +
        rankMassOffset hn ht ha z) := by
  exact (MvMass.rename_le _ _).trans ((MvTwoParameterCoefficient.mass _ _ _).trans
    (rank_principal_mass hn ht ha hR0 power negative z j hc hg))

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
