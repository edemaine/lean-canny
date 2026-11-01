/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.BoundedGateZeroSpace
/-! # The literal bounded compiler has a proper component-preserving projection -/
@[expose] public section
namespace LeanCanny.Connectivity.BoundedGateCoordinates
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open MonotoneGateSource MonotoneGateGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def projection (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) (y : NativeZero F c) :=
  BoundedWeakBooleanWitness.projection (radius F c) (MonotoneGateCircles.atomValue F c)
    (MonotoneGateCircles.predicate F c) (MonotoneGateArithmetic.predicate_mono F c hk)
    (zeroWitnessHomeomorph F c ha hk y)

theorem projection_old (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) (y : NativeZero F c) (i : Fin (F.dimension c)) :
    (projection F c ha hk y).val i=y.val ⟨i.val,by
      have H:=i.isLt
      change i.val < F.dimension c+2*F.count c+F.count c+2*F.count c
      omega⟩ := rfl

theorem continuous_projection (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) : Continuous (projection F c ha hk) :=
  (BoundedWeakBooleanWitness.continuous_projection _ _ _ _).comp
    (zeroWitnessHomeomorph F c ha hk).continuous

theorem proper_projection (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) : IsProperMap (projection F c ha hk) := by
  have HP := BoundedWeakBooleanWitness.proper_projection (radius F c) (MonotoneGateCircles.atomValue F c)
    (MonotoneGateCircles.predicate F c) (MonotoneGateArithmetic.predicate_mono F c hk) (radius_continuous F c)
    (FiniteMonotoneClosed.isClosed _ (fun i => isClosed_eq
      ((MonotoneGateCircles.atom_continuous F c i).comp continuous_fst)
      (((continuous_fst.comp ((continuous_apply i).comp continuous_snd)).norm).pow 2))
      _ (MonotoneGateArithmetic.predicate_mono F c hk))
  exact HP.comp (zeroWitnessHomeomorph F c ha hk).isProperMap

private theorem homeomorph_joined {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x y : X) : JoinedIn univ x y ↔ JoinedIn univ (e x) (e y) := by
  constructor
  · intro H
    exact (H.map e.continuous.continuousOn).mono (subset_univ _)
  · intro H
    simpa only [Homeomorph.symm_apply_apply] using (H.map e.symm.continuous.continuousOn).mono (subset_univ _)

theorem joined_iff (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) (y z : NativeZero F c) :
    JoinedIn univ y z ↔ JoinedIn univ (projection F c ha hk y) (projection F c ha hk z) :=
  (homeomorph_joined (zeroWitnessHomeomorph F c ha hk) y z).trans
    (BoundedWeakBooleanWitness.joined_iff _ _ _ (MonotoneGateArithmetic.predicate_mono F c hk)
      (atom_radius F c) (radius_continuous F c) (MonotoneGateCircles.atom_continuous F c) _ _)

theorem preconnected_iff (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) :
    IsPreconnected (univ : Set (NativeZero F c)) ↔ IsPreconnected
      (univ : Set (WeakBooleanWitness.Base (MonotoneGateCircles.atomValue F c) (MonotoneGateCircles.predicate F c))) := by
  have HE := (zeroWitnessHomeomorph F c ha hk).isPreconnected_image (s := univ)
  rw [Set.image_univ_of_surjective (zeroWitnessHomeomorph F c ha hk).surjective] at HE
  exact HE.symm.trans (BoundedWeakBooleanWitness.preconnected_iff _ _ _
    (MonotoneGateArithmetic.predicate_mono F c hk) (atom_radius F c)
    (radius_continuous F c) (MonotoneGateCircles.atom_continuous F c))

end LeanCanny.Connectivity.BoundedGateCoordinates
