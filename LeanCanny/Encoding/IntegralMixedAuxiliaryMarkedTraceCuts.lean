/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTraceCutAll
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordBank
public import LeanCanny.Algebra.IntegralMixedFramedPlannedProbe
/-! # Original-only validity of every actual cut in a marked record trace

The complete sampler uses the full literal script followed by one default-X
birth. Every cut is checked at a suffix of that one joint terminal tuple.
The native costs come from the actual original marked-record backend.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedTraceCuts
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)
local notation "P" => certifiedParameters hn ht ha hR
local notation "D" => certifiedPlan hn ht ha hR
local notation "H" => certifiedData hn ht ha hR
local notation "L" => (fun _ : List Bool=>3)
local notation "F" => factor hn ht ha
local notation "C" => IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR
local notation "HS" => certifiedInputs hn ht ha hR

noncomputable def probeControls : IntegralMixedFramedCurrentQNativeBits.Controls
    (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
    (IntegralMixedFramedCutProbeTransportBits.plan P D L F C)
    (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) :=
  IntegralMixedFramedPlannedProbe.controls (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    L F C (callerControls hn ht ha hR)

theorem probeBounds : IntegralMixedFramedCurrentQNativeBits.Bounds
    (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
    (IntegralMixedFramedCutProbeTransportBits.plan P D L F C)
    (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) (probeControls hn ht ha hR) :=
  IntegralMixedFramedPlannedProbe.bounds (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    L F C (callerControls hn ht ha hR) (callerBounds hn ht ha hR)

noncomputable def input := IntegralFramedTraceCutSource.input P D H L F C HS
noncomputable def Validated (q : List Bool) : Prop := IntegralFramedTraceCutAll.Validated P D H L F C HS q
noncomputable def language : Language := {q | Validated hn ht ha hR q}

attribute [local irreducible] probeControls IntegralMixedFramedHistoryFamilyBits.family

theorem decider : SpaceDecider (language hn ht ha hR) :=
  IntegralFramedTraceCutAll.decider P D H L F C HS (factor_positive hn ht ha)
    (certifiedBounds hn ht ha hR).fallback (certifiedAccess hn ht ha hR)
    (BinaryFn.const 3) (factor_binary hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed_binary hn ht ha hR)
    (certifiedControls hn ht ha hR).normalization (probeControls hn ht ha hR) (probeBounds hn ht ha hR)
    (callerData hn ht ha hR) (callerControls hn ht ha hR) (callerBounds hn ht ha hR)

theorem mem_PSPACE : language hn ht ha hR∈PSPACE := (decider hn ht ha hR).mem_PSPACE

/-- Exact selected-parent validity, recorded degree and untruncated root
conditions, with the embedding fixed by the same terminal tuple. -/
theorem validated_iff (q : List Bool) : q∈language hn ht ha hR ↔
    ∃ hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (pairFst q) (pairSnd q),
      ∀ j<IntegralFramedTraceCutMetadata.length P D (pairFst q),
        IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D (pairFst q) j).command →
        IntegralFramedTraceCutExact.Compatible P D H L F C HS (pairFst q) (List.replicate j true) (pairSnd q) hv := Iff.rfl

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedTraceCuts
