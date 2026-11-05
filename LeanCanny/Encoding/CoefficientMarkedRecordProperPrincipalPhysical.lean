/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalMap
/-! # Proper principal slices use the actual terminal physical scalar columns -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientTarskiParameterQueries
open Polynomial
open LeanCanny.Encoding
open scoped Classical

theorem slice_map {R S : Type*} [CommRing R] [CommRing S] {m : ℕ} (φ : R →+* S)
    (p : MvPolynomial (Fin (m+2)) R) (delta epsilon : ℕ) :
    MvPolynomial.map φ (MvTwoParameterCoefficient.slice p delta epsilon) =
      MvTwoParameterCoefficient.slice (MvPolynomial.map φ p) delta epsilon := by
  apply MvPolynomial.ext
  intro v
  simp only [MvPolynomial.coeff_map, MvTwoParameterCoefficient.coefficient]

noncomputable def castVariables {R : Type*} [CommRing R] {m k : ℕ} (h : m = k)
    (p : MvPolynomial (Fin m) R) : MvPolynomial (Fin k) R := MvPolynomial.rename (Fin.cast h) p

theorem castVariables_map {R S : Type*} [CommRing R] [CommRing S] {m k : ℕ} (φ : R →+* S)
    (h : m = k) (p : MvPolynomial (Fin m) R) :
    MvPolynomial.map φ (castVariables h p) = castVariables h (MvPolynomial.map φ p) :=
  MvPolynomial.map_rename _ _ _

theorem castVariables_heq {m k a b : ℕ} (h : m = k) (h' : a = b)
    (p : MvPolynomial (Fin m) ℤ) (q : MvPolynomial (Fin a) ℤ) (hm : m = a) (hp : HEq p q) :
    HEq (castVariables h p) (castVariables h' q) := by
  cases hm
  cases eq_of_heq hp
  cases h
  cases h'
  rfl

noncomputable def scalarAt {R : Type*} [CommRing R] (d : CoefficientMarkedRecordRows.Data R) (i : ℕ) : ℕ :=
  if hi : i < d.birth then (d.scalar ⟨i, hi⟩).val else 0

noncomputable def scalarApply {R : Type*} [CommRing R] {m : ℕ} (d : CoefficientMarkedRecordRows.Data R)
    (p : MvPolynomial (Fin m) R) : MvPolynomial ℕ R := MvPolynomial.rename (fun i => scalarAt d i.val) p

theorem scalarApply_map {R S : Type*} [CommRing R] [CommRing S] {m : ℕ} (φ : R →+* S)
    (d : CoefficientMarkedRecordRows.Data R) (p : MvPolynomial (Fin m) R) :
    MvPolynomial.map φ (scalarApply d p) =
      scalarApply (CoefficientMarkedRecordRows.map φ d) (MvPolynomial.map φ p) :=
  MvPolynomial.map_rename _ _ _

theorem scalarApply_heq {m k : ℕ} (d e : CoefficientMarkedRecordRows.Data ℤ)
    (p : MvPolynomial (Fin m) ℤ) (q : MvPolynomial (Fin k) ℤ)
    (hm : m = k) (hd : d = e) (hp : HEq p q) : scalarApply d p = scalarApply e q := by
  cases hm
  cases hd
  cases eq_of_heq hp
  rfl

theorem slice_heq {m k : ℕ} (p : MvPolynomial (Fin (m+2)) ℤ)
    (q : MvPolynomial (Fin (k+2)) ℤ) (hm : m = k) (hp : HEq p q) (delta epsilon : ℕ) :
    HEq (MvTwoParameterCoefficient.slice p delta epsilon) (MvTwoParameterCoefficient.slice q delta epsilon) := by
  cases hm
  cases eq_of_heq hp
  rfl

noncomputable def physicalData (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) : CoefficientMarkedRecordRows.Data ℤ :=
  ⟨IntegralFramedPhysicalSquare.count P D key, (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key,
    (IntegralFramedPhysicalSquare.sampler P D H key).rows, (IntegralFramedPhysicalSquare.sampler P D H key).scalar⟩

theorem physicalData_planned (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (key : List Bool) :
    physicalData (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key = physicalData P D H key := rfl

theorem scalarApply_native (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (p : MvPolynomial (Fin (IntegralMixedFramedBankSnapshotBits.atKey P D H key).count) ℤ) :
    scalarApply (physicalData P D H key) p = MvPolynomial.rename Fin.val
      (MvPolynomial.rename (IntegralMixedFramedScalarEmbedding.scalarMap P D H key) p) := by
  rw [MvPolynomial.rename_rename]
  apply congrArg (fun f => MvPolynomial.rename f p)
  funext i
  have hi : i.val < (physicalData P D H key).birth := i.isLt
  unfold scalarAt
  rw [dite_eq_left hi]
  rfl

end LeanCanny.Algebra.CoefficientTarskiParameterQueries

namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR Polynomial
open CoefficientTarskiParameterQueries
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data certifiedParameters certifiedPlan certifiedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R0 : List Bool → ℕ} (hR0 : BinaryFn R0)
local notation "PC" => certifiedParameters hn ht ha (radius_binary hR0)
local notation "DC" => certifiedPlan hn ht ha (radius_binary hR0)
local notation "HC" => certifiedData hn ht ha (radius_binary hR0)

noncomputable def properPhysicalData (mean : Bool) (z : List Bool) :=
  CoefficientMarkedRecordRows.symbolic hn ht ha (catalogRoot n mean z)
    (IntegralMixedCausalRecordPlanBits.count (catalogRoot n mean z)) le_rfl

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed CoefficientMarkedRecordRows.symbolic

theorem proper_terminal_physical_data (mean : Bool) (z : List Bool)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n mean z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)) :
    CoefficientMarkedRecordRows.map
      (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)))
      (properPhysicalData hn ht ha mean z) = physicalData PC DC HC (terminal hn ht ha hR0 mean z) := by
  let ctx := catalogRoot n mean z
  have HM := CoefficientMarkedRecordRows.map_indexed hn ht ha ctx
    (IntegralMixedOriginalRegularSource.radius R0) (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] hR
  have HK : CoefficientMarkedRecordRowLayout.key (n := n) ctx (IntegralMixedCausalRecordPlanBits.count ctx) [] =
      catalogTerminal n mean z := by
    unfold CoefficientMarkedRecordRowLayout.key catalogTerminal IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
    rw [CoefficientMarkedPreludeActual.indices_length]
  have HI : CoefficientMarkedRecordRows.indexed hn ht ha ctx
      (IntegralMixedOriginalRegularSource.radius R0) (IntegralMixedCausalRecordPlanBits.count ctx) [] =
      physicalData (parameters hn ht ha) (plan hn ht ha (IntegralMixedOriginalRegularSource.radius R0))
        (data hn ht ha (IntegralMixedOriginalRegularSource.radius R0)) (catalogTerminal n mean z) := by
    unfold CoefficientMarkedRecordRows.indexed
    rw [HK]
    rfl
  rw [HI, ← physicalData_planned _ _ _ _ _ _ _, ← terminal_catalog hn ht ha hR0 mean z] at HM
  exact HM

noncomputable def properNearPhysical (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (j delta epsilon : ℕ) :=
  scalarApply (properPhysicalData hn ht ha false z) (MvTwoParameterCoefficient.slice
    (castVariables (by omega : 1+(IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n false z)+1) =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n false z)+2)
      (properNearPrincipal hn ht ha right power eta eps z hc j)) delta epsilon)

noncomputable def properRankPhysical (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (j delta epsilon : ℕ) :=
  scalarApply (properPhysicalData hn ht ha true z)
    (MvTwoParameterCoefficient.slice (properRankPrincipal hn ht ha power eps z hc j) delta epsilon)

theorem proper_near_physical_map (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n false z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)) (j delta epsilon : ℕ) :
    MvPolynomial.map
      (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)))
      (properNearPhysical hn ht ha right power eta eps z hc j delta epsilon) =
      MvPolynomial.rename Fin.val (nearPhysicalPrincipal hn ht ha hR0 right power eta eps z j delta epsilon) := by
  have HP := proper_near_principal_map hn ht ha hR0 right power eta eps z hc hg hR j
  have HA := (principal_terminal_count hn ht ha hR0 false z).symm
  have HC' := castVariables_heq
    (by omega : 1+(IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n false z)+1) =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n false z)+2)
    (near_dimensions hn ht ha hR0 right power eta eps z) _ _ (congrArg (fun m => 1+(m+1)) HA) HP
  have HS := slice_heq _ _ HA HC' delta epsilon
  have HX := scalarApply_heq _ _ _ _ HA (proper_terminal_physical_data hn ht ha hR0 false z hR) HS
  have HN := scalarApply_native PC DC HC (terminal hn ht ha hR0 false z)
    (MvTwoParameterCoefficient.slice (castVariables (near_dimensions hn ht ha hR0 right power eta eps z)
      (FixedWidthTarskiPrincipalBits.polynomial (nearFamily hn ht ha hR0 right power eta eps) z j)) delta epsilon)
  unfold properNearPhysical
  rw [scalarApply_map, slice_map, castVariables_map]
  exact HX.trans HN

theorem proper_rank_physical_map (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n true z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n true z)) (j delta epsilon : ℕ) :
    MvPolynomial.map
      (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n true z)))
      (properRankPhysical hn ht ha power eps z hc j delta epsilon) =
      MvPolynomial.rename Fin.val (rankPhysicalPrincipal hn ht ha hR0 power eps z j delta epsilon) := by
  have HP := proper_rank_principal_map hn ht ha hR0 power eps z hc hg hR j
  have HA := (principal_terminal_count hn ht ha hR0 true z).symm
  have HS := slice_heq _ _ HA HP delta epsilon
  have HX := scalarApply_heq _ _ _ _ HA (proper_terminal_physical_data hn ht ha hR0 true z hR) HS
  have HN := scalarApply_native PC DC HC (terminal hn ht ha hR0 true z)
    (MvTwoParameterCoefficient.slice
      (FixedWidthTarskiPrincipalBits.polynomial (rankFamily hn ht ha hR0 power eps) z j) delta epsilon)
  unfold properRankPhysical
  rw [scalarApply_map, slice_map]
  exact HX.trans HN

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
