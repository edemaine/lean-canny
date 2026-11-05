/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusRowHeight
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeadHeight
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusWindowHeight
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedPlan

/-! # Affine profiles for the actual certified marked family

Planning changes numeric packet clipping. Heads are bounded directly with the
actual certified parser; no equality of base and certified heads is asserted.
At explicit family keys, physical rows and retained-coordinate windows agree.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan
  (parameters plan data factor certifiedParameters certifiedPlan certifiedData)
open IntegralMixedFramedNormalizationBits (planned plannedPlan plannedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem planning_rows (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ) (key : List Bool) (G : ℕ)
    (HB : ∀ i, MvMass.mass (((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).sampler.rows i) ≤ 2 ^ G) :
    ∀ i, MvMass.mass (((IntegralMixedFramedHistoryFamilyBits.family (planned P L F C)
      (plannedPlan P D L F C) (plannedData P D H L F C)).state key).sampler.rows i) ≤ 2 ^ G := HB

private theorem planning_inputs (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (L0 F0 C0 L F C : List Bool → ℕ) (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) :
    IntegralMixedFramedStepHeight.FamilyInputs (planned P L0 F0 C0) (plannedPlan P D L0 F0 C0) L F C where
  script := h.script
  default := h.default

private theorem planning_fallback (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L0 F0 C0 L C : List Bool → ℕ) (key : List Bool) :
    IntegralMixedFramedOriginalBounds.FallbackBounds (planned P L0 F0 C0) (plannedPlan P D L0 F0 C0)
      (plannedData P D H L0 F0 C0) L C key ↔
        IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key := by
  cases hc : (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;>
    simp only [IntegralMixedFramedOriginalBounds.FallbackBounds,
      IntegralMixedFramedNormalizationBits.planned_instruction, plannedData, hc]

private theorem head_mass_bound (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ)
    (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hF : ∀ root, 1 ≤ F root)
    (hf : ∀ key, IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (parent terminal : List Bool → List Bool) (d e : List Bool → ℕ) (q : List Bool) (y : ℕ) :
    MvMass.mass ((IntegralMixedFramedTerminalCoordinateHeadBits.polynomial P D H parent terminal d e q).coeff y) ≤
      2 ^ ((P.cap (RankedHistoryTask.root (parent q)) + 1) * P.width (RankedHistoryTask.root (parent q)) +
        IntegralMixedFramedRawHeight.rootCeiling P L F C (RankedHistoryTask.root (parent q)) + (e q + 1).size) := by
  have HM := IntegralMixedFramedTerminalCoordinateHeadBits.coefficient_mass P D H L F C h hF hf parent terminal d e q y
  apply HM.trans (Nat.pow_le_pow_right (by decide) ?_)
  let key := IntegralMixedVirtualTaskBits.saved P (parent q)
  have HB : (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key ≤ P.cap (pairFst key) + 1 := by
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
    exact min_le_right _ _
  have HE := Nat.mul_le_mul_right (P.width (pairFst key)) HB
  unfold IntegralMixedFramedCoordinatePackedBits.headMassBound IntegralMixedFramedCoordinatePackedBits.oldMassBound
  have HR : pairFst key = RankedHistoryTask.root (parent q) := by simp only [key, IntegralMixedVirtualTaskBits.saved, pairFst_pair]
  have HW : (IntegralMixedFramedHistoryFamilyBits.family P D H).width key = P.width (pairFst key) := by
    unfold IntegralMixedFramedHistoryFamilyBits.family
    rfl
  change (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key *
    (IntegralMixedFramedHistoryFamilyBits.family P D H).width key + _ + _ ≤ _
  rw [HW]
  rw [HR] at HE ⊢
  omega

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan
  IntegralMixedSourceIntegerRecordAppend.data IntegralMixedAuxiliaryMarkedIntegerPlan.seed
  IntegralMixedFramedHistoryFamilyBits.family

theorem certified_full_row_mass {R : List Bool → ℕ} (hR : BinaryFn R) (key : List Bool)
    (i : (IntegralMixedFramedHistoryFamilyBits.family (certifiedParameters hn ht ha hR)
      (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)).physical key) :
    MvMass.mass (((IntegralMixedFramedHistoryFamilyBits.family (certifiedParameters hn ht ha hR)
      (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)).state key).sampler.rows i) ≤
      2 ^ (rowSlope hn ht ha (pairFst key) * R (pairFst key) + rowOffset hn ht ha (pairFst key)) :=
  planning_rows (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (fun _ => 3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) key _
    (full_row_mass hn ht ha R key) i

theorem certified_affine_inputs {R : List Bool → ℕ} (hR : BinaryFn R) :
    IntegralMixedFramedStepHeight.FamilyInputs (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
      (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) :=
  planning_inputs (parameters hn ht ha) (plan hn ht ha R)
    (fun _ => 3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) (familyInputs hn ht ha R)

theorem certified_head_coefficient_mass {R : List Bool → ℕ} (hR : BinaryFn R)
    (parent terminal : List Bool → List Bool) (d e : List Bool → ℕ) (q : List Bool) (y : ℕ) :
    MvMass.mass ((IntegralMixedFramedTerminalCoordinateHeadBits.polynomial
      (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)
      parent terminal d e q).coeff y) ≤
      2 ^ (rawSlope hn ht ha (pairFst (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (parent q))) *
        R (pairFst (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (parent q))) + headOffset hn ht ha parent e q) := by
  have HI := planning_inputs (parameters hn ht ha) (plan hn ht ha R)
    (fun _ => 3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) (familyInputs hn ht ha R)
  have HF : ∀ key, IntegralMixedFramedOriginalBounds.FallbackBounds (certifiedParameters hn ht ha hR)
      (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) (fun _ => 3) (seed hn ht ha R) key := fun key =>
    (planning_fallback (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
      (fun _ => 3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
      (fun _ => 3) (seed hn ht ha R) key).mpr (fallback_bounds hn ht ha R key)
  have HM := head_mass_bound (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
    (certifiedData hn ht ha hR) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) HI
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor_positive hn ht ha) HF parent terminal d e q y
  apply HM.trans (Nat.pow_le_pow_right (by decide) ?_)
  have HC : IntegralMixedFramedRawHeight.rootCeiling (certifiedParameters hn ht ha hR)
      (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) (RankedHistoryTask.root (parent q)) =
    IntegralMixedFramedRawHeight.rootCeiling (parameters hn ht ha)
      (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) (RankedHistoryTask.root (parent q)) := rfl
  rw [HC, raw_ceiling_affine]
  simp only [headOffset, IntegralMixedVirtualTaskBits.saved, pairFst_pair]
  change ((parameters hn ht ha).cap _ + 1) * (parameters hn ht ha).width _ + _ + _ ≤ _
  omega

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
