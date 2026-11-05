/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutTerminalHead
public import LeanCanny.Encoding.CoefficientMarkedRecordProperWindow
/-! # Actual terminal-bank windows for full-cut comparisons -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutWindow
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open CoefficientTarskiParameterQueries
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data certifiedParameters certifiedPlan certifiedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

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

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def weight (ctx : List Bool) (index : ℕ) :=
  UniformIntegralPowerSchedule.birth ((parameters hn ht ha).cap ctx+1) (2^(parameters hn ht ha).width ctx)
    (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx-1-min index (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx))

noncomputable def polynomial (ctx : List Bool) (index : ℕ) (negative : Bool) :=
  window (m := IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx)
    (CoefficientMarkedRecordBankProducts.common hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx))
    (CoefficientMarkedRecordBankProducts.cofactor hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) index)
    index (weight hn ht ha ctx index) negative

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed

variable {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "PC" => certifiedParameters hn ht ha hR
local notation "DC" => certifiedPlan hn ht ha hR
local notation "HC" => certifiedData hn ht ha hR
local notation "TERM" => CoefficientMarkedRecordRawCutMetadata.terminal (n := n)
local notation "F" => IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha
local notation "C" => IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR
local notation "HS" => IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha hR

theorem terminal_products (ctx : List Bool) (index : ℕ)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    (CoefficientMarkedRecordBankProducts.common hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx)).eval ((2 : ℤ)^R ctx) =
      (IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (TERM ctx)).common ∧
    (CoefficientMarkedRecordBankProducts.cofactor hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) index).eval ((2 : ℤ)^R ctx) =
      (IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (TERM ctx)).cofactor index := by
  have HQ := CoefficientMarkedRecordBankProducts.common_specializes hn ht ha ctx R
    (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] hlarge
  have HA := CoefficientMarkedRecordBankProducts.cofactor_specializes hn ht ha ctx R
    (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] hlarge index
  have HP := CoefficientMarkedRecordBankProducts.snapshot_planned (parameters hn ht ha)
    (plan hn ht ha R) (data hn ht ha R) (fun _ => 3) F C (TERM ctx)
  change (IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (TERM ctx)) = _ at HP
  change _ = (IntegralMixedFramedBankSnapshotBits.atKey (parameters hn ht ha)
    (plan hn ht ha R) (data hn ht ha R) (TERM ctx)).common at HQ
  change _ = (IntegralMixedFramedBankSnapshotBits.atKey (parameters hn ht ha)
    (plan hn ht ha R) (data hn ht ha R) (TERM ctx)).cofactor index at HA
  rw [← HP] at HQ HA
  exact ⟨HQ, HA⟩

theorem weight_native (ctx : List Bool) (index : ℕ) :
    (IntegralMixedFramedWindowQuery.family PC DC HC (fun _ => 3) F C HS
      (fun _ => TERM ctx) (fun _ => index)).weight [] = weight hn ht ha ctx index := by
  change IntegralMixedFramedBankCoordinateBits.weight PC DC HC
    (IntegralMixedFramedBankSnapshotBits.packet (TERM ctx) [] index 0) = _
  rw [weight_packet, CoefficientMarkedRecordRawCutMetadata.terminal_count hn ht ha hR ctx]
  rw [show pairFst (TERM ctx) = ctx from CoefficientMarkedRecordRowLayout.key_root _ _ _]
  rfl

theorem specializes (ctx : List Bool) (index : ℕ) (negative : Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    HEq ((polynomial hn ht ha ctx index negative).map (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))))
      (IntegralMixedFramedWindowQuery.polynomial PC DC HC (fun _ => 3) F C HS
        (fun _ => TERM ctx) (fun _ => index) negative []) := by
  obtain ⟨HQ, HA⟩ := terminal_products hn ht ha hR ctx index hlarge
  change (evalRingHom ((2 : ℤ)^R ctx)) _ = _ at HQ HA
  have HM := (CoefficientMarkedRecordRawCutMetadata.terminal_count hn ht ha hR ctx).symm
  have HW := (weight_native hn ht ha hR ctx index).symm
  unfold polynomial
  rw [window_map]
  have HN := window_native PC DC HC (fun _ => 3) F C HS
    (fun _ => TERM ctx) (fun _ => index) negative []
  exact (window_heq _ _ _ _ _ _ _ _ HM HQ HA HW).trans (heq_of_eq HN)

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutWindow
