/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.BoundedGateProjection
/-! # Surjectivity of the literal bounded projection from its canonical section -/
@[expose] public section
namespace LeanCanny.Connectivity.BoundedGateCoordinates
open ETR Set LeanCanny.Encoding LeanCanny.Geometry MonotoneGateSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem projection_surjective (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) : Function.Surjective (projection F c ha hk) := by
  intro x
  let w := BoundedWeakBooleanWitness.centerSection (radius F c) (MonotoneGateCircles.atomValue F c)
    (MonotoneGateCircles.predicate F c) (MonotoneGateArithmetic.predicate_mono F c hk) (atom_radius F c) x
  refine ⟨(zeroWitnessHomeomorph F c ha hk).symm w,?_⟩
  unfold projection
  rw [Homeomorph.apply_symm_apply]
  rfl

end LeanCanny.Connectivity.BoundedGateCoordinates
