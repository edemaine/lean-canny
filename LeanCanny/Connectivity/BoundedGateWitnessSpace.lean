/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.BoundedGateBudget
/-! # Bounded gate witnesses and their exact circular coordinates -/
@[expose] public section
namespace LeanCanny.Connectivity.BoundedGateCoordinates
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open MonotoneGateSource MonotoneGateGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Witness (F : Family) (c : List Bool) := BoundedWeakBooleanWitness.Space
  (radius F c) (MonotoneGateCircles.atomValue F c) (MonotoneGateCircles.predicate F c)

noncomputable abbrev TightSpace (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) :=
  {z : (ZeroSet F c) × (Fin (F.count c) → CircularWitness.Plane) //
    ∀ i, ‖(circles F c ha hk z.1).val.2 i‖^2+‖z.2 i‖^2=
      radius F c (circles F c ha hk z.1).val.1}

noncomputable def witnessHomeomorph (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) : TightSpace F c ha hk ≃ₜ Witness F c where
  toFun z := ⟨((circles F c ha hk z.val.1).val.1,
    fun i => ((circles F c ha hk z.val.1).val.2 i,z.val.2 i)),
      ⟨z.property,(circles F c ha hk z.val.1).property⟩⟩
  invFun z := ⟨((MonotoneGateCircles.zeroWitnessHomeomorph F c ha hk).symm
    ⟨(z.val.1,fun i => (z.val.2 i).1),z.property.2⟩,fun i => (z.val.2 i).2),by
      simpa only [circles,Homeomorph.apply_symm_apply] using z.property.1⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · change (MonotoneGateCircles.zeroWitnessHomeomorph F c ha hk).symm
        (MonotoneGateCircles.zeroWitnessHomeomorph F c ha hk z.val.1)=z.val.1
      exact Homeomorph.symm_apply_apply _ _
    · rfl
  right_inv z := by
    apply Subtype.ext
    change ((MonotoneGateCircles.zeroWitnessHomeomorph F c ha hk
      ((MonotoneGateCircles.zeroWitnessHomeomorph F c ha hk).symm _)).val.1,
      fun i => ((MonotoneGateCircles.zeroWitnessHomeomorph F c ha hk
      ((MonotoneGateCircles.zeroWitnessHomeomorph F c ha hk).symm _)).val.2 i,(z.val.2 i).2))=z.val
    rw [Homeomorph.apply_symm_apply]
  continuous_toFun := by
    have HE : Continuous (fun z : TightSpace F c ha hk => circles F c ha hk z.val.1) :=
      (MonotoneGateCircles.zeroWitnessHomeomorph F c ha hk).continuous.comp
        (continuous_fst.comp continuous_subtype_val)
    exact ((continuous_fst.comp (continuous_subtype_val.comp HE)).prodMk
      (continuous_pi (fun i => ((continuous_apply i).comp
        (continuous_snd.comp (continuous_subtype_val.comp HE))).prodMk
        ((continuous_apply i).comp (continuous_snd.comp continuous_subtype_val))))).subtype_mk _
  continuous_invFun := by
    have HA : Continuous (fun z : Witness F c =>
        (⟨(z.val.1,fun i => (z.val.2 i).1),z.property.2⟩ :
          WeakBooleanWitness.Space (MonotoneGateCircles.atomValue F c) (MonotoneGateCircles.predicate F c))) :=
      ((continuous_fst.comp continuous_subtype_val).prodMk
        (continuous_pi (fun i => continuous_fst.comp ((continuous_apply i).comp
          (continuous_snd.comp continuous_subtype_val))))).subtype_mk _
    exact (((MonotoneGateCircles.zeroWitnessHomeomorph F c ha hk).symm.continuous.comp HA).prodMk
      (continuous_pi (fun i => continuous_snd.comp ((continuous_apply i).comp
        (continuous_snd.comp continuous_subtype_val))))).subtype_mk _

end LeanCanny.Connectivity.BoundedGateCoordinates
