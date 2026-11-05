/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusCertifiedHeight
public import LeanCanny.Algebra.IntegralMixedFramedFullCutTerminalReader
/-! # Affine coefficient mass for the actual certified full selected factor head -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data factor certifiedParameters certifiedPlan certifiedData)
open IntegralMixedFramedNormalizationBits (planned plannedPlan plannedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem fallback_planned (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L0 F0 C0 L C : List Bool → ℕ) (key : List Bool) :
    IntegralMixedFramedOriginalBounds.FallbackBounds (planned P L0 F0 C0) (plannedPlan P D L0 F0 C0)
      (plannedData P D H L0 F0 C0) L C key ↔
        IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key := by
  cases hc : (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;>
    simp only [IntegralMixedFramedOriginalBounds.FallbackBounds,
      IntegralMixedFramedNormalizationBits.planned_instruction, plannedData, hc]

attribute [local irreducible] IntegralMixedFramedFullCutTerminalHead.polynomial

private theorem full_head_mass (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ)
    (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hF : ∀ root, 1 ≤ F root)
    (hf : ∀ key, IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (parent terminal : List Bool → List Bool) (d : List Bool → ℕ) (q : List Bool) (y : ℕ) :
    MvMass.mass ((IntegralMixedFramedFullCutTerminalHead.polynomial P D H parent terminal d q).coeff y) ≤
      2^((P.cap (RankedHistoryTask.root (parent q))+1)*P.width (RankedHistoryTask.root (parent q)) +
        IntegralMixedFramedRawHeight.rootCeiling P L F C (RankedHistoryTask.root (parent q))) := by
  have HM := IntegralMixedFramedFullCutTerminalHead.coefficient_mass P D H parent terminal d L F C h hF hf q y
  apply HM.trans (Nat.pow_le_pow_right (by decide) ?_)
  let key := IntegralMixedVirtualTaskBits.saved P (parent q)
  have HB : (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key ≤ P.cap (pairFst key)+1 := by
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
    exact min_le_right _ _
  have HE := Nat.mul_le_mul_right (P.width (pairFst key)) HB
  have HR : pairFst key = RankedHistoryTask.root (parent q) := by
    simp only [key, IntegralMixedVirtualTaskBits.saved, pairFst_pair]
  have HW : (IntegralMixedFramedHistoryFamilyBits.family P D H).width key = P.width (pairFst key) := rfl
  change (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key *
    (IntegralMixedFramedHistoryFamilyBits.family P D H).width key +
      IntegralMixedFramedRawHeight.rootCeiling P L F C (pairFst key) ≤ _
  rw [HW]
  rw [HR] at HE ⊢
  omega

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan
  IntegralMixedSourceIntegerRecordAppend.data IntegralMixedAuxiliaryMarkedIntegerPlan.seed
  IntegralMixedFramedHistoryFamilyBits.family

/-- The actual saved parent is retained in the radius charge. No polynomial,
normalization or coefficient-height model is supplied. -/
theorem certified_full_cut_head_coefficient_mass {R : List Bool → ℕ} (hR : BinaryFn R)
    (parent terminal : List Bool → List Bool) (d : List Bool → ℕ) (q : List Bool) (y : ℕ) :
    MvMass.mass ((IntegralMixedFramedFullCutTerminalHead.polynomial
      (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)
      parent terminal d q).coeff y) ≤
      2^(rawSlope hn ht ha (pairFst (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (parent q))) *
        R (pairFst (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (parent q))) +
        headOffset hn ht ha parent (fun _ => 0) q) := by
  have HF : ∀ key, IntegralMixedFramedOriginalBounds.FallbackBounds (certifiedParameters hn ht ha hR)
      (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) (fun _ => 3) (seed hn ht ha R) key := fun key =>
    (fallback_planned (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
      (fun _ => 3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
      (fun _ => 3) (seed hn ht ha R) key).mpr (fallback_bounds hn ht ha R key)
  have HM := full_head_mass (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
    (certifiedData hn ht ha hR) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R)
    (certified_affine_inputs hn ht ha hR) (IntegralMixedAuxiliaryMarkedRecordPlan.factor_positive hn ht ha) HF
    parent terminal d q y
  apply HM.trans (Nat.pow_le_pow_right (by decide) ?_)
  have HC : IntegralMixedFramedRawHeight.rootCeiling (certifiedParameters hn ht ha hR)
      (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) (RankedHistoryTask.root (parent q)) =
      IntegralMixedFramedRawHeight.rootCeiling (parameters hn ht ha)
      (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) (RankedHistoryTask.root (parent q)) := rfl
  rw [HC, raw_ceiling_affine]
  simp only [headOffset, IntegralMixedVirtualTaskBits.saved, pairFst_pair]
  change ((parameters hn ht ha).cap _+1)*(parameters hn ht ha).width _+_ ≤ _
  omega

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
