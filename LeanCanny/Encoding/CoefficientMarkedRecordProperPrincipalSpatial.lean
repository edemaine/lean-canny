/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalPhysical
/-! # Original physical spatial boxes for constructed proper principal queries -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientTarskiParameterQueries
open LeanCanny.Computation LeanCanny.Encoding
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family FixedWidthTarskiPrincipalBits.polynomial
variable (P : IntegralCriticalHistoryTask.Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
  (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ)
  (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (parent terminal : List Bool → List Bool) (center selected : List Bool → ℕ)

theorem near_width_unary (a : IntegralCriticalHistoryTask.Access P)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (IntegralMixedFramedHistoryFamilyBits.family P D H))
    (hp : parent ∈ FP) (ht : terminal ∈ FP) (hc : BinaryFn center) (hi : BinaryFn selected) :
    UnaryFn (IntegralFramedTerminalTarskiStatistic.mf P D H L F C hs parent terminal center selected 0 false false).width := by
  have HB := IntegralFramedTerminalTarskiStatistic.budget_binary P D H L F C hs parent terminal center selected a I hp ht hc hi
  dsimp only [IntegralFramedTerminalTarskiStatistic.mf, IntegralMixedFramedTerminalTarskiFamilyBits.family,
    IntegralMixedFramedTerminalTarskiFamilyBits.width]
  change UnaryFn (fun z => (IntegralFramedTerminalTarskiStatistic.budget P D H L F C hs parent terminal center selected z).size)
  exact (UnaryFn.length HB.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

theorem near_principal_lt_width (power : Fin 3) (eta eps : Bool) (z : List Bool) (j : ℕ) :
    (FixedWidthTarskiPrincipalBits.polynomial
      (IntegralFramedTerminalTarskiStatistic.mf P D H L F C hs parent terminal center selected power eta eps) z j).totalDegree <
      2^(IntegralFramedTerminalTarskiStatistic.mf P D H L F C hs parent terminal center selected power eta eps).width z := by
  have HB := IntegralMixedFramedTerminalTarskiFamilyBits.principal_degree P D H L F C hs parent terminal
    (IntegralMixedSelectedCoordinateHead.fullDegree P (IntegralMixedFramedHistoryFamilyBits.family P D H) parent)
    (IntegralMixedSelectedCoordinateHead.fullParameter P parent) center selected (fun _ => power) eta eps z j
  dsimp only [IntegralFramedTerminalTarskiStatistic.mf, IntegralMixedFramedTerminalTarskiFamilyBits.family,
    IntegralMixedFramedTerminalTarskiFamilyBits.width]
  dsimp only [IntegralMixedFramedTerminalTarskiFamilyBits.family] at HB
  exact HB.trans_lt (Nat.lt_size_self _)

omit center in
theorem rank_principal_lt_width (power : Fin 3) (eps : Bool) (z : List Bool) (j : ℕ) :
    (FixedWidthTarskiPrincipalBits.polynomial
      (IntegralFramedZeroTarskiStatistic.mf P D H L F C hs parent terminal selected power eps) z j).totalDegree <
      2^(IntegralFramedZeroTarskiStatistic.mf P D H L F C hs parent terminal selected power eps).width z := by
  have HB := IntegralMixedFramedZeroTarskiBits.principal_degree P D H L F C hs parent terminal
    (IntegralMixedSelectedCoordinateHead.fullDegree P (IntegralMixedFramedHistoryFamilyBits.family P D H) parent)
    (IntegralMixedSelectedCoordinateHead.fullParameter P parent) selected (fun _ => power) eps z j
  exact HB.trans_lt (Nat.lt_size_self _)

theorem physical_slice_degree {m k a : ℕ} (p : MvPolynomial (Fin m) ℤ) (h : m = k+2)
    (column : Fin k → Fin a) (delta epsilon : ℕ) :
    (MvPolynomial.rename column (MvTwoParameterCoefficient.slice
      (MvTwoParameterEncodedCoefficient.castPolynomial h p) delta epsilon)).totalDegree ≤ p.totalDegree :=
  (MvPolynomial.totalDegree_rename_le _ _).trans ((MvTwoParameterCoefficient.degree _ _ _).trans
    (MvTwoParameterEncodedCoefficient.cast_degree _ _))

theorem physical_slice_degree' {m a : ℕ} (p : MvPolynomial (Fin (m+2)) ℤ)
    (column : Fin m → Fin a) (delta epsilon : ℕ) :
    (MvPolynomial.rename column (MvTwoParameterCoefficient.slice p delta epsilon)).totalDegree ≤ p.totalDegree :=
  (MvPolynomial.totalDegree_rename_le _ _).trans (MvTwoParameterCoefficient.degree _ _ _)

end LeanCanny.Algebra.CoefficientTarskiParameterQueries

namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR Polynomial
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedRecordPlan (certifiedParameters certifiedPlan certifiedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed

noncomputable def properNearSpatialDegree (right : Bool) (z : List Bool) :=
  2^(nearFamily hn ht ha (BinaryFn.const 0) right 0 false false).width z
noncomputable def properRankSpatialDegree (z : List Bool) :=
  2^(rankFamily hn ht ha (BinaryFn.const 0) 0 false).width z

local notation "B0" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary (BinaryFn.const 0)) false
local notation "A0" => IntegralMixedPhysicalMarkedPlan.native hn ht ha (radius_binary (BinaryFn.const 0)) false

theorem properNearSpatialDegree_binary (right : Bool) : BinaryFn (properNearSpatialDegree hn ht ha right) := by
  have HW := CoefficientTarskiParameterQueries.near_width_unary
    (B0).parameters (B0).plan (B0).data (B0).nodes (B0).factor (B0).seed (B0).bounds
    (parent hn ht ha (BinaryFn.const 0) false) (terminal hn ht ha (BinaryFn.const 0) false)
    (centerIndex hn ht ha (BinaryFn.const 0) right) (pointIndex hn ht ha (BinaryFn.const 0) false false)
    (A0).parameters (metadata hn ht ha (BinaryFn.const 0))
    (parent_FP hn ht ha (BinaryFn.const 0) false) (terminal_FP hn ht ha (BinaryFn.const 0) false)
    (centerIndex_binary hn ht ha (BinaryFn.const 0) right) (pointIndex_binary hn ht ha (BinaryFn.const 0) false false)
  unfold properNearSpatialDegree
  rw [nearFamily_installed]
  exact (BinaryFn.const 2).powUnary HW

theorem properRankSpatialDegree_binary : BinaryFn (properRankSpatialDegree hn ht ha) := by
  have HB := IntegralFramedZeroTarskiStatistic.budget_binary
    (B0).parameters (B0).plan (B0).data (B0).nodes (B0).factor (B0).seed (B0).bounds
    (parent hn ht ha (BinaryFn.const 0) true) (terminal hn ht ha (BinaryFn.const 0) true)
    (pointIndex hn ht ha (BinaryFn.const 0) true true)
    (A0).parameters (metadata hn ht ha (BinaryFn.const 0))
    (parent_FP hn ht ha (BinaryFn.const 0) true) (terminal_FP hn ht ha (BinaryFn.const 0) true)
    (pointIndex_binary hn ht ha (BinaryFn.const 0) true true)
  have HW : UnaryFn (rankFamily hn ht ha (BinaryFn.const 0) 0 false).width :=
    (UnaryFn.length HB.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact (BinaryFn.const 2).powUnary HW

variable {R0 : List Bool → ℕ} (hR0 : BinaryFn R0)
local notation "PC" => certifiedParameters hn ht ha (radius_binary hR0)
local notation "DC" => certifiedPlan hn ht ha (radius_binary hR0)
local notation "HC" => certifiedData hn ht ha (radius_binary hR0)

theorem proper_near_native_spatial_degree (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (j delta epsilon : ℕ) :
    (nearPhysicalPrincipal hn ht ha hR0 right power eta eps z j delta epsilon).totalDegree ≤
      properNearSpatialDegree hn ht ha right z := by
  have HT := CoefficientTarskiParameterQueries.near_principal_lt_width PC DC HC (fun _ => 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0))
    (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false) (centerIndex hn ht ha hR0 right)
    (pointIndex hn ht ha hR0 false false) power eta eps z j
  change (FixedWidthTarskiPrincipalBits.polynomial (nearFamily hn ht ha hR0 right power eta eps) z j).totalDegree <
      2^(nearFamily hn ht ha hR0 right power eta eps).width z at HT
  rw [near_width_catalog hn ht ha hR0 right power eta eps z hc hg,
    ← near_width_catalog hn ht ha (BinaryFn.const 0) right 0 false false z hc hg] at HT
  exact (CoefficientTarskiParameterQueries.physical_slice_degree _ (near_dimensions hn ht ha hR0 right power eta eps z)
    (IntegralMixedFramedScalarEmbedding.scalarMap PC DC HC (terminal hn ht ha hR0 false z)) delta epsilon).trans HT.le

theorem proper_rank_native_spatial_degree (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (j delta epsilon : ℕ) :
    (rankPhysicalPrincipal hn ht ha hR0 power eps z j delta epsilon).totalDegree ≤
      properRankSpatialDegree hn ht ha z := by
  have HT := CoefficientTarskiParameterQueries.rank_principal_lt_width PC DC HC (fun _ => 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0))
    (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true) (pointIndex hn ht ha hR0 true true)
    power eps z j
  change (FixedWidthTarskiPrincipalBits.polynomial (rankFamily hn ht ha hR0 power eps) z j).totalDegree <
      2^(rankFamily hn ht ha hR0 power eps).width z at HT
  rw [rank_width_catalog hn ht ha hR0 power eps z hc hg,
    ← rank_width_catalog hn ht ha (BinaryFn.const 0) 0 false z hc hg] at HT
  exact (CoefficientTarskiParameterQueries.physical_slice_degree' _
    (IntegralMixedFramedScalarEmbedding.scalarMap PC DC HC (terminal hn ht ha hR0 true z)) delta epsilon).trans HT.le

private theorem zero_of_dyadic_tail (p : ℤ[X]) (C : ℕ)
    (h : ∀ r, C ≤ r → p.eval ((2 : ℤ)^r) = 0) : p = 0 := by
  have HD := IntegerPolynomialDyadic.natDegree_le p C 0 0 (fun r hr => by
    rw [h r hr]
    exact Nat.zero_le _)
  have HConstant := Polynomial.eq_C_of_natDegree_le_zero HD
  have HE := h C le_rfl
  rw [HConstant, Polynomial.eval_C] at HE
  rw [HConstant, HE, Polynomial.C_0]

private theorem spatial_degree_of_dyadic_tail {σ : Type*} (p : MvPolynomial σ ℤ[X]) (C E : ℕ)
    (h : ∀ r, C ≤ r → (p.map (evalRingHom ((2 : ℤ)^r))).totalDegree ≤ E) : p.totalDegree ≤ E := by
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro v hv
  by_contra he
  have HVD : E < v.sum (fun _ e => e) := by omega
  have HZ : p.coeff v = 0 := zero_of_dyadic_tail (p.coeff v) C (fun r hr => by
    have HH := MvPolynomial.coeff_eq_zero_of_totalDegree_lt ((h r hr).trans_lt HVD)
    simpa only [MvPolynomial.coeff_map, Polynomial.coe_evalRingHom] using HH)
  exact (MvPolynomial.mem_support_iff.mp hv) HZ

omit hR0 in
theorem proper_near_spatial_degree (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (j delta epsilon : ℕ) :
    (properNearPhysical hn ht ha right power eta eps z hc j delta epsilon).totalDegree ≤
      properNearSpatialDegree hn ht ha right z := by
  apply spatial_degree_of_dyadic_tail _ (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
    (catalogRoot n false z))
  intro r hr
  have HS := proper_near_physical_map hn ht ha (BinaryFn.const r) right power eta eps z hc hg hr j delta epsilon
  dsimp only [IntegralMixedOriginalRegularSource.radius] at HS
  rw [HS]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (proper_near_native_spatial_degree hn ht ha (BinaryFn.const r) right power eta eps z hc hg j delta epsilon)

omit hR0 in
theorem proper_rank_spatial_degree (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (j delta epsilon : ℕ) :
    (properRankPhysical hn ht ha power eps z hc j delta epsilon).totalDegree ≤
      properRankSpatialDegree hn ht ha z := by
  apply spatial_degree_of_dyadic_tail _ (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
    (catalogRoot n true z))
  intro r hr
  have HS := proper_rank_physical_map hn ht ha (BinaryFn.const r) power eps z hc hg hr j delta epsilon
  dsimp only [IntegralMixedOriginalRegularSource.radius] at HS
  rw [HS]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (proper_rank_native_spatial_degree hn ht ha (BinaryFn.const r) power eps z hc hg j delta epsilon)

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
