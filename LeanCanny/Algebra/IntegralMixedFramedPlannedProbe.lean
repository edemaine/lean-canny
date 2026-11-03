/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPlanningAbsorption
public import LeanCanny.Algebra.BoundedRegularIntegerCurrentQRootControls
/-! # A certified caller backend also serves the full-factor probes

The base has already been planned with this exact profile. Planning again
after attaching an arbitrary caller modulus therefore changes no parameter,
instruction or fallback selection. Native controls are transported as one
complete dependent package; sampler labels are never reindexed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPlannedProbe
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedNormalizationBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ)
local notation "Q" => planned P L F C
local notation "E" => plannedPlan P D L F C
local notation "J" => plannedData P D H L F C
local notation "A" => IntegralMixedFramedCutProbeTransportBits.lifted Q
local notation "B" => IntegralMixedFramedCutProbeTransportBits.liftedPlan Q E
local notation "K" => IntegralMixedFramedCutProbeTransportBits.liftedData Q E J

private theorem height_fixed : IntegralMixedFramedRawHeight.rootCeiling A (L∘pairFst) (F∘pairFst) (C∘pairFst)= (A).height := by
  funext root
  rfl
private theorem modulus_fixed (root : List Bool) :
    requiredModulus A (L∘pairFst) (F∘pairFst) (C∘pairFst) root≤(A).modulusBound root := by
  change requiredModulus A (L∘pairFst) (F∘pairFst) (C∘pairFst) root≤
    max ((planned P L F C).modulusBound (pairFst root)) (IntegralMixedFramedModulusPacket.extra root)
  rw [BoundedRegularIntegerCurrentQBits.requiredModulus_pullback]
  exact (planned_budget P L F C (pairFst root)).trans (le_max_left _ _)

theorem parameters_eq : IntegralMixedFramedCutProbeTaskBits.parameters Q L F C=A :=
  IntegralMixedFramedPlanningAbsorption.parameters A (L∘pairFst) (F∘pairFst) (C∘pairFst)
    (height_fixed P L F C) (modulus_fixed P L F C)
theorem plan_heq : HEq (IntegralMixedFramedCutProbeTransportBits.plan Q E L F C) B :=
  IntegralMixedFramedPlanningAbsorption.plan_heq A B (L∘pairFst) (F∘pairFst) (C∘pairFst)
    (height_fixed P L F C) (modulus_fixed P L F C)
theorem data_heq : HEq (IntegralMixedFramedCutProbeTransportBits.data Q E J L F C) K :=
  IntegralMixedFramedPlanningAbsorption.data_heq A B K (L∘pairFst) (F∘pairFst) (C∘pairFst)
    (height_fixed P L F C) (modulus_fixed P L F C)

noncomputable def controls (c : IntegralMixedFramedCurrentQNativeBits.Controls A B K) :
    IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters Q L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan Q E L F C)
      (IntegralMixedFramedCutProbeTransportBits.data Q E J L F C) :=
  IntegralMixedFramedPlanningAbsorption.controlsTransport (parameters_eq P L F C)
    (plan_heq P D L F C) (data_heq P D H L F C) c

theorem bounds (c : IntegralMixedFramedCurrentQNativeBits.Controls A B K)
    (hc : IntegralMixedFramedCurrentQNativeBits.Bounds A B K c) :
    IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters Q L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan Q E L F C)
      (IntegralMixedFramedCutProbeTransportBits.data Q E J L F C) (controls P D H L F C c) :=
  IntegralMixedFramedPlanningAbsorption.boundsTransport (parameters_eq P L F C)
    (plan_heq P D L F C) (data_heq P D H L F C) c hc
end LeanCanny.Algebra.IntegralMixedFramedPlannedProbe
