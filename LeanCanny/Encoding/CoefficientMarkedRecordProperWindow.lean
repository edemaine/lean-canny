/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperTerminalHead
public import LeanCanny.Encoding.CoefficientMarkedRecordBankProducts
/-! # Constructed terminal-bank windows for the actual proper queries -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientTarskiParameterQueries
theorem window_heq {m k : ℕ} (q a q' a' : ℤ) (index w w' : ℕ) (negative : Bool)
    (hm : m = k) (hq : q = q') (ha : a = a') (hw : w = w') :
    HEq (window (m := m) q a index w negative) (window (m := k) q' a' index w' negative) := by
  cases hm
  cases hq
  cases ha
  cases hw
  rfl
theorem window_arity (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool → List Bool) (index : List Bool → ℕ) (z : List Bool) :
    (IntegralMixedFramedWindowQuery.family P D H L F C hs key index).arity z =
      (IntegralMixedFramedBankSnapshotBits.atKey P D H (key z)).count := rfl

theorem window_denominator (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool → List Bool) (index : List Bool → ℕ) (z : List Bool) :
    (IntegralMixedFramedWindowQuery.family P D H L F C hs key index).scalars.denominator z =
      (IntegralMixedFramedBankSnapshotBits.atKey P D H (key z)).common := rfl

theorem window_numerator (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool → List Bool) (index : List Bool → ℕ) (z : List Bool) :
    (IntegralMixedFramedWindowQuery.family P D H L F C hs key index).scalars.numerator z =
      (IntegralMixedFramedBankSnapshotBits.atKey P D H (key z)).cofactor (index z) := rfl

theorem window_native (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool → List Bool) (index : List Bool → ℕ) (negative : Bool) (z : List Bool) :
    window (m := (IntegralMixedFramedBankSnapshotBits.atKey P D H (key z)).count)
      (IntegralMixedFramedBankSnapshotBits.atKey P D H (key z)).common
      ((IntegralMixedFramedBankSnapshotBits.atKey P D H (key z)).cofactor (index z)) (index z)
      ((IntegralMixedFramedWindowQuery.family P D H L F C hs key index).weight z) negative =
      IntegralMixedFramedWindowQuery.polynomial P D H L F C hs key index negative z := rfl

end LeanCanny.Algebra.CoefficientTarskiParameterQueries

namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR Polynomial
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

noncomputable def properCommon (mean : Bool) (z : List Bool) :=
  CoefficientMarkedRecordBankProducts.common hn ht ha (catalogRoot n mean z)
    (IntegralMixedCausalRecordPlanBits.count (catalogRoot n mean z))

noncomputable def properCofactor (mean : Bool) (index : List Bool → ℕ) (z : List Bool) :=
  CoefficientMarkedRecordBankProducts.cofactor hn ht ha (catalogRoot n mean z)
    (IntegralMixedCausalRecordPlanBits.count (catalogRoot n mean z)) (index z)

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed

theorem proper_terminal_products (mean : Bool) (z : List Bool) (index : List Bool → ℕ)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n mean z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)) :
    (properCommon hn ht ha mean z).eval ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)) =
      (IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (terminal hn ht ha hR0 mean z)).common ∧
    (properCofactor hn ht ha mean index z).eval ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)) =
      (IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (terminal hn ht ha hR0 mean z)).cofactor (index z) := by
  let ctx := catalogRoot n mean z
  have HQ := CoefficientMarkedRecordBankProducts.common_specializes hn ht ha ctx
    (IntegralMixedOriginalRegularSource.radius R0) (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] hR
  have HA := CoefficientMarkedRecordBankProducts.cofactor_specializes hn ht ha ctx
    (IntegralMixedOriginalRegularSource.radius R0) (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] hR (index z)
  have HK : CoefficientMarkedRecordRowLayout.key (n := n) ctx (IntegralMixedCausalRecordPlanBits.count ctx) [] =
      catalogTerminal n mean z := by
    unfold CoefficientMarkedRecordRowLayout.key catalogTerminal IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
    rw [CoefficientMarkedPreludeActual.indices_length]
  rw [HK] at HQ HA
  have HS : IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (catalogTerminal n mean z) =
      IntegralMixedFramedBankSnapshotBits.atKey (parameters hn ht ha)
        (plan hn ht ha (IntegralMixedOriginalRegularSource.radius R0))
        (data hn ht ha (IntegralMixedOriginalRegularSource.radius R0)) (catalogTerminal n mean z) :=
    CoefficientMarkedRecordBankProducts.snapshot_planned _ _ _ _ _ _ _
  rw [← HS, ← terminal_catalog hn ht ha hR0 mean z] at HQ HA
  exact ⟨HQ, HA⟩

noncomputable def properWindow (mean : Bool) (index : List Bool → ℕ) (negative : Bool) (z : List Bool) :=
  CoefficientTarskiParameterQueries.window
    (m := IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n mean z))
    (properCommon hn ht ha mean z) (properCofactor hn ht ha mean index z) (index z)
    (catalogWindowWeight hn ht ha mean index z) negative

theorem proper_window_specializes (mean : Bool) (index : List Bool → ℕ) (negative : Bool) (z : List Bool)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n mean z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)) :
    HEq ((properWindow hn ht ha mean index negative z).map (MvPolynomial.map
      (Polynomial.evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)))))
      (IntegralMixedFramedWindowQuery.polynomial PC DC HC (fun _ => 3)
        (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
        (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0))
        (terminal hn ht ha hR0 mean) index negative z) := by
  obtain ⟨HQ, HA⟩ := proper_terminal_products hn ht ha hR0 mean z index hR
  change (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)))
    (properCommon hn ht ha mean z) = _ at HQ
  change (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)))
    (properCofactor hn ht ha mean index z) = _ at HA
  have HCount := (principal_terminal_count hn ht ha hR0 mean z).symm
  have HW := (principal_window_weight hn ht ha hR0 mean index z).symm
  unfold properWindow
  rw [CoefficientTarskiParameterQueries.window_map]
  have HN := CoefficientTarskiParameterQueries.window_native PC DC HC (fun _ => 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (radius_binary hR0))
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha (radius_binary hR0))
    (terminal hn ht ha hR0 mean) index negative z
  exact (CoefficientTarskiParameterQueries.window_heq _ _ _ _ _ _ _ _ HCount HQ HA HW).trans (heq_of_eq HN)

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
