/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalPhysical
public import Mathlib.Algebra.MvPolynomial.Variables
/-! # Proper physical principals use only the original full sampler variable box -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientTarskiParameterQueries
open LeanCanny.Encoding
open scoped Classical
theorem scalarApply_vars {R : Type*} [CommRing R] {m : ℕ} (d : CoefficientMarkedRecordRows.Data R)
    (hpos : 0 < d.count) (p : MvPolynomial (Fin m) R) :
    (scalarApply d p).vars ⊆ Finset.range d.count := by
  intro j hj
  obtain ⟨i, _, rfl⟩ := MvPolynomial.mem_vars_rename (fun i : Fin m => scalarAt d i.val) p hj
  apply Finset.mem_range.mpr
  unfold scalarAt
  split_ifs with hi
  · exact (d.scalar ⟨i.val, hi⟩).isLt
  · exact hpos
end LeanCanny.Algebra.CoefficientTarskiParameterQueries

namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR Polynomial
open CoefficientTarskiParameterQueries
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed CoefficientMarkedRecordRows.symbolic

theorem proper_physical_count_pos (mean : Bool) (z : List Bool) :
    0 < (properPhysicalData hn ht ha mean z).count := by
  let C := CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n mean z)
  have HR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n mean z) ≤
      IntegralMixedOriginalRegularSource.radius (fun _ => C) (catalogRoot n mean z) := le_rfl
  have HM := proper_terminal_physical_data hn ht ha (BinaryFn.const C) mean z HR
  have HB := congrArg (fun d : CoefficientMarkedRecordRows.Data ℤ => d.birth) HM
  change (properPhysicalData hn ht ha mean z).birth = _ at HB
  have HP : 0 < (properPhysicalData hn ht ha mean z).birth := by
    rw [HB]
    exact positive hn ht ha (BinaryFn.const C) mean z
  exact lt_of_le_of_lt (Nat.zero_le _) ((properPhysicalData hn ht ha mean z).scalar ⟨0, HP⟩).isLt

theorem proper_physical_count_metadata (mean : Bool) (z : List Bool) :
    (properPhysicalData hn ht ha mean z).count = IntegralFramedPhysicalSquare.count
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (IntegralMixedOriginalRegularSource.radius_binary (BinaryFn.const 0)) false).parameters
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (IntegralMixedOriginalRegularSource.radius_binary (BinaryFn.const 0)) false).plan
      (terminal hn ht ha (BinaryFn.const 0) mean z) := by
  let ctx := catalogRoot n mean z
  let R := IntegralMixedOriginalRegularSource.radius (fun _ => 0)
  have HK : CoefficientMarkedRecordRowLayout.key (n := n) ctx (IntegralMixedCausalRecordPlanBits.count ctx) [] =
      catalogTerminal n mean z := by
    unfold CoefficientMarkedRecordRowLayout.key catalogTerminal IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
    rw [CoefficientMarkedPreludeActual.indices_length]
  have HL := CoefficientMarkedRecordRowLayout.count_eq hn ht ha ctx R
    (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl []
  rw [HK] at HL
  have HF : (properPhysicalData hn ht ha mean z).count =
      (CoefficientMarkedRecordRowLayout.fixed hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count := by
    simp only [properPhysicalData, CoefficientMarkedRecordRows.symbolic, CoefficientMarkedRecordRows.prefixData]
    rfl
  have HL' := HL.trans HF.symm
  have HS := congrArg (fun d : CoefficientMarkedRecordRows.Data ℤ => d.count)
    (physicalData_planned (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
      (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha
        (IntegralMixedOriginalRegularSource.radius_binary (BinaryFn.const 0))) (catalogTerminal n mean z))
  change IntegralFramedPhysicalSquare.count _ _ _ = IntegralFramedPhysicalSquare.count _ _ _ at HS
  have HX := HL'.symm.trans HS.symm
  rw [← terminal_catalog hn ht ha (BinaryFn.const 0) mean z] at HX
  exact HX

theorem proper_physical_count_unary (mean : Bool) : UnaryFn (fun z => (properPhysicalData hn ht ha mean z).count) :=
  (sampler_access hn ht ha (BinaryFn.const 0) mean).count.of_eq
    (fun z => (proper_physical_count_metadata hn ht ha mean z).symm)

theorem proper_near_variable_box (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (j delta epsilon : ℕ) :
    (properNearPhysical hn ht ha right power eta eps z hc j delta epsilon).vars ⊆
      Finset.range (properPhysicalData hn ht ha false z).count :=
  scalarApply_vars _ (proper_physical_count_pos hn ht ha false z) _

theorem proper_rank_variable_box (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (j delta epsilon : ℕ) :
    (properRankPhysical hn ht ha power eps z hc j delta epsilon).vars ⊆
      Finset.range (properPhysicalData hn ht ha true z).count :=
  scalarApply_vars _ (proper_physical_count_pos hn ht ha true z) _

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
