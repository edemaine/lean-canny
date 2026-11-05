/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutPrincipalHeight
public import LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalVariables
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalBranchSign
/-! # Full-cut principal slices on the actual full physical scalar columns -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutPhysical
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open CoefficientTarskiParameterQueries
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data certifiedParameters certifiedPlan certifiedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def rawData (ctx : List Bool) :=
  CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl
noncomputable def polynomial (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (index : ℕ) (power : Fin 3) (negative : Bool) (j delta epsilon : ℕ) :=
  scalarApply (rawData hn ht ha ctx) (MvTwoParameterCoefficient.slice
    (castVariables (by omega : 1+(IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx+1) =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx+2)
      (CoefficientMarkedRecordFullCutPrincipal.polynomial hn ht ha ctx k hk index power negative j)) delta epsilon)

variable {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "PC" => certifiedParameters hn ht ha hR
local notation "DC" => certifiedPlan hn ht ha hR
local notation "HC" => certifiedData hn ht ha hR
local notation "TERM" => CoefficientMarkedRecordRawCutMetadata.terminal (n := n)
local notation "G" => CoefficientMarkedRecordFullCutPrincipal.nativeFamily hn ht ha hR

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed CoefficientMarkedRecordRows.symbolic

theorem terminal_data (ctx : List Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    CoefficientMarkedRecordRows.map (evalRingHom ((2 : ℤ)^R ctx)) (rawData hn ht ha ctx) =
      physicalData PC DC HC (TERM ctx) := by
  have HM := CoefficientMarkedRecordRows.map_indexed hn ht ha ctx R
    (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] hlarge
  have HI : CoefficientMarkedRecordRows.indexed hn ht ha ctx R (IntegralMixedCausalRecordPlanBits.count ctx) [] =
      physicalData (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) (TERM ctx) := rfl
  rw [HI, ← physicalData_planned _ _ _ _ _ _ _] at HM
  exact HM

theorem dimensions (ctx : List Bool) (k index : ℕ) (power : Fin 3) (negative : Bool) :
    (G ctx k index power negative).arity [] =
      (IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (TERM ctx)).count+2 := by
  change 1+((IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (TERM ctx)).count+1) =
    (IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (TERM ctx)).count+2
  omega

noncomputable def native (ctx : List Bool) (k index : ℕ) (power : Fin 3) (negative : Bool) (j delta epsilon : ℕ) :=
  MvPolynomial.rename (IntegralMixedFramedScalarEmbedding.scalarMap PC DC HC (TERM ctx))
    (MvTwoParameterCoefficient.slice (castVariables (dimensions hn ht ha hR ctx k index power negative)
      (FixedWidthTarskiPrincipalBits.polynomial (G ctx k index power negative) [] j)) delta epsilon)

theorem specializes (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (index : ℕ) (power : Fin 3) (negative : Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) (j delta epsilon : ℕ) :
    MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))
      (polynomial hn ht ha ctx k hk index power negative j delta epsilon) =
      MvPolynomial.rename Fin.val (native hn ht ha hR ctx k index power negative j delta epsilon) := by
  have HP := CoefficientMarkedRecordFullCutPrincipal.specializes hn ht ha hR ctx k hk hc index power negative hlarge j
  have HA := (CoefficientMarkedRecordRawCutMetadata.terminal_count hn ht ha hR ctx).symm
  have HC' := castVariables_heq
    (by omega : 1+(IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx+1) = IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx+2)
    (dimensions hn ht ha hR ctx k index power negative) _ _ (congrArg (fun m => 1+(m+1)) HA) HP
  have HX := scalarApply_heq _ _ _ _ HA (terminal_data hn ht ha hR ctx hlarge)
    (slice_heq _ _ HA HC' delta epsilon)
  have HN := scalarApply_native PC DC HC (TERM ctx)
    (MvTwoParameterCoefficient.slice (castVariables (dimensions hn ht ha hR ctx k index power negative)
      (FixedWidthTarskiPrincipalBits.polynomial (G ctx k index power negative) [] j)) delta epsilon)
  unfold polynomial
  rw [scalarApply_map, slice_map, castVariables_map]
  exact HX.trans HN

theorem native_mass (ctx : List Bool) (k index : ℕ) (negative : Bool) (j delta epsilon : ℕ) :
    MvMass.mass (native hn ht ha hR ctx k index 1 negative j delta epsilon) ≤
      2^(CoefficientMarkedRecordFullCutPrincipalHeight.slope hn ht ha ctx k*R ctx+
        CoefficientMarkedRecordFullCutPrincipalHeight.offset hn ht ha ctx k) :=
  (MvMass.rename_le _ _).trans ((MvTwoParameterCoefficient.mass _ _ _).trans
    ((MvMass.rename_le _ _).trans (CoefficientMarkedRecordFullCutPrincipalHeight.principal_mass hn ht ha hR ctx k index negative j)))

omit hR in
theorem count_unary : UnaryFn (fun ctx => (rawData hn ht ha ctx).count) :=
  CoefficientMarkedRecordCriticalBranchSign.count_unary hn ht ha

omit hR in
theorem count_pos (ctx : List Bool) : 0 < (rawData hn ht ha ctx).count := by
  let C := CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx
  have HM := terminal_data hn ht ha (BinaryFn.const C) ctx le_rfl
  have HB := congrArg (fun d : CoefficientMarkedRecordRows.Data ℤ => d.birth) HM
  change (rawData hn ht ha ctx).birth =
    (IntegralMixedFramedBankSnapshotBits.atKey (certifiedParameters hn ht ha (BinaryFn.const C))
      (certifiedPlan hn ht ha (BinaryFn.const C)) (certifiedData hn ht ha (BinaryFn.const C)) (TERM ctx)).count at HB
  rw [CoefficientMarkedRecordRawCutMetadata.terminal_count] at HB
  have HP : 0 < (rawData hn ht ha ctx).birth := by
    rw [HB]
    unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
    omega
  exact lt_of_le_of_lt (Nat.zero_le _) ((rawData hn ht ha ctx).scalar ⟨0, HP⟩).isLt

omit hR in
theorem variable_box (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (index : ℕ) (power : Fin 3) (negative : Bool) (j delta epsilon : ℕ) :
    (polynomial hn ht ha ctx k hk index power negative j delta epsilon).vars ⊆ Finset.range (rawData hn ht ha ctx).count :=
  scalarApply_vars _ (count_pos hn ht ha ctx) _

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutPhysical
