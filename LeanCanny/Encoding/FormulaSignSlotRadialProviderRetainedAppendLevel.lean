/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendWindows
public import LeanCanny.Geometry.IntegralMixedChronologicalRetainedLevel
/-! # A concrete retained pair from the actual provider parent word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedChronologicalFrame IntegralMixedChronologicalEndpoint IntegralMixedFrozenFrame
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderIntegerSource.source parentState parentTuple parentValues

theorem parent_horizon (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    (parentCommands old hv hd e he).length≤(P).cap (preparedRoot old e)+1 := by
  rw [parentCommands,FormulaSignSlotRadialProviderRecordContinuation.beforeCommands_length]
  exact FormulaSignSlotRadialProviderRecordPrefix.bound _ _ (prefix_fit old hv hd e he)

noncomputable def parentHom (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :=
  Classical.choose (parent_interpretation old hv hd e he)

theorem parentHom_generators (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    ∀i,parentHom old hv hd e he ((parentState old hv hd e he).sampler.scalarPrefix.basis.generator i)=
      parentTuple old hv hd e he ((parentState old hv hd e he).sampler.scalar i)^
        UniformIntegralPowerSchedule.weights ((P).cap (preparedRoot old e)+1) (2^(P).width (preparedRoot old e))
          (parentCommands old hv hd e he).length i :=
  (Classical.choose_spec (parent_interpretation old hv hd e he)).1

theorem parentHom_quotients (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    ∀i,parentHom old hv hd e he ((parentState old hv hd e he).bank.numerator i)/
      ((parentState old hv hd e he).bank.denominator i:ℝ)=parentValues old hv hd e he i :=
  by simpa only [parentValues,parentHom] using (Classical.choose_spec (parent_interpretation old hv hd e he)).2

noncomputable def childCoordinate (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) : Fin ((P).ambient (preparedRoot old e)+1) :=
  ⟨(parentDescriptor old hv hd e he).labels.length+1,by
    have H := parent_descriptor_nonterminal old hv hd e he
    omega⟩

theorem child_coordinate_free (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    childCoordinate old hv hd e he∉(line (parentDescriptor old hv hd e he).frame
      (IntegralMixedChronologicalSweepFrame.next (parentDescriptor old hv hd e he)
        (parent_descriptor_fit old hv hd e he))).frozen := by
  change childCoordinate old hv hd e he∉insert _ (parentDescriptor old hv hd e he).frame.frozen
  rw [Finset.mem_insert,not_or]
  constructor
  · intro h
    have H := congrArg Fin.val h
    change (parentDescriptor old hv hd e he).labels.length+1=(parentDescriptor old hv hd e he).labels.length at H
    omega
  · rw [Descriptor.frozen_mem]
    change ¬(parentDescriptor old hv hd e he).labels.length+1<(parentDescriptor old hv hd e he).labels.length
    omega

noncomputable def retainedNativePair (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :=
  @retainedPair ((P).ambient (preparedRoot old e)) ((P).cap (preparedRoot old e)+1)
    ((P).width (preparedRoot old e)) (parentCommands old hv hd e he).length
    (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old e))
    (Index (Fin 0) (parentCommands old hv hd e he)) (indexFintype (Fin 0) (parentCommands old hv hd e he))
    (parentState old hv hd e he) (parent_horizon old hv hd e he)
    (FormulaSignSlotRadialProviderRecordPlan.positive (preparedRoot old e))
    (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap (preparedRoot old e))
    (parentDescriptor old hv hd e he) (parentTuple old hv hd e he) (parent_roots old hv hd e he)
    (parentHom old hv hd e he) (parentHom_generators old hv hd e he) (parentValues old hv hd e he)
    (parentHom_quotients old hv hd e he) (IntegralMixedChronologicalMidpoint.reference (endpointLabel old hv hd e he))

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
