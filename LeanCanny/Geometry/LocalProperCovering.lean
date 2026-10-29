/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Maps.Proper.Basic

/-! # Coverings from properness on an open target

Local charts and properness are needed only on the retained open parameter
set. Behavior of an auxiliary equation at excluded parameters is irrelevant.
-/

@[expose] public section
namespace LeanCanny.Geometry.LocalProperCovering
open Set Topology
set_option backward.isDefEq.respectTransparency false
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

lemma localHomeomorph_restrict {f : X → Y} (hf : Continuous f) {s : Set Y} (hs : IsOpen s)
    (hl : IsLocalHomeomorphOn f (f ⁻¹' s)) : IsLocalHomeomorph (s.restrictPreimage f) := by
  have hi : IsLocalHomeomorph (Subtype.val : (f ⁻¹' s) → X) :=
    (hs.preimage hf).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hc : IsLocalHomeomorph (f ∘ (Subtype.val : (f ⁻¹' s) → X)) := by
    apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    exact hl.comp hi.isLocalHomeomorphOn (fun x _ => x.property)
  change IsLocalHomeomorph ((Subtype.val : s → Y) ∘ s.restrictPreimage f) at hc
  exact hc.of_comp hs.isOpenEmbedding_subtypeVal.isLocalHomeomorph hf.restrictPreimage

lemma finite_fiber {f : X → Y} (hp : IsProperMap f) (hl : IsLocalHomeomorph f) (y : Y) :
    (f ⁻¹' {y}).Finite := by
  apply (hp.isCompact_preimage isCompact_singleton).finite
  apply IsDiscrete.of_openPartialHomeomorph f subset_rfl
  intro x _
  obtain ⟨e, he, hf⟩ := hl x
  exact ⟨e, he, hf.symm⟩

variable [T2Space X]

lemma covering_restrict {f : X → Y} (hf : Continuous f) {s : Set Y} (hs : IsOpen s)
    (hp : IsProperMap (s.restrictPreimage f)) (hl : IsLocalHomeomorphOn f (f ⁻¹' s)) :
    IsCoveringMap (s.restrictPreimage f) := by
  have hlocal := localHomeomorph_restrict hf hs hl
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply hp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
  · intro y _
    exact finite_fiber hp hlocal y
  · exact hlocal.isLocalHomeomorphOn

end LeanCanny.Geometry.LocalProperCovering
