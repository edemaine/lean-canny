/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.BoundedRegularComponents
public import LeanCanny.Geometry.LiftPaths

/-! # Marking the regular-source components that represent original zeros

A single polynomial marks the source points whose old coordinates lie in
the sphere zero set. Every marked point is joined to the constructed lift
of its original projection. Original connectedness can therefore be checked
only between marked points, allowing other source components to be ignored.
No assertion that every source component meets the marked set is needed.
-/

@[expose] public section
namespace LeanCanny.Geometry.BoundedRegularSource
open MvPolynomial Set LeanCanny.Algebra BoundedZeroSource

variable {n : ℕ}

noncomputable def oldBase (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (z : Zeros q D b R) :
    CircleSublevelLift.Base (scaledEnergy q D b R) (level n D b R) :=
  PurePowerSublevelLift.projection (powerHalfDegree D) (powerHalfDegree_odd D)
    (scaledEnergy q D b R) (level n D b R) (levelHomeomorph q D b R z)

theorem oldBase_apply (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (z : Zeros q D b R) (i : Fin (n + 2)) :
    (oldBase q D b R z).val i = z.val (i.castAdd 2) := by
  change (BoundedZeroSource.coordinates.symm z.val).1 i = z.val (i.castAdd 2)
  have h := congrArg (fun w : Fin (n + 4) → ℝ => w (i.castAdd 2))
    (BoundedZeroSource.coordinates.apply_symm_apply z.val)
  simpa only [BoundedZeroSource.coordinates_apply, Fin.append_left] using h

noncomputable def markPolynomial (q : MvPolynomial (Fin n) ℤ) (R : ℕ) : MvPolynomial (Fin (n + 4)) ℤ :=
  rename (Fin.castAdd 2) (BoundedZeroSource.polynomial q R)

theorem eval_mark (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (z : Zeros q D b R) :
    (markPolynomial q R).eval₂ (Int.castRingHom ℝ) z.val =
      (BoundedZeroSource.polynomial q R).eval₂ (Int.castRingHom ℝ) (oldBase q D b R z).val := by
  rw [markPolynomial, eval₂_rename]
  apply congrArg ((BoundedZeroSource.polynomial q R).eval₂ (Int.castRingHom ℝ))
  funext i
  exact (oldBase_apply q D b R z i).symm

noncomputable def Marked (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) :=
  {z : Zeros q D b R | (markPolynomial q R).eval₂ (Int.castRingHom ℝ) z.val = 0}

noncomputable def oldPoint (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (z : Marked q D b R) :
    BoundedZeroSource.Zeros q R :=
  ⟨(oldBase q D b R z.val).val, (eval_mark q D b R z.val).symm.trans z.property⟩

noncomputable def markedProjection (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (z : Marked q D b R) : Bounded q R :=
  BoundedZeroSource.projection q R (oldPoint q D b R z)

theorem oldBase_lift (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (x : Bounded q R) :
    oldBase q D b R (lift q D b R x) = basePoint q D b R x := by
  simp only [oldBase, lift, Homeomorph.apply_symm_apply, PurePowerSublevelLift.projection_section]

noncomputable def markedLift (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (x : Bounded q R) : Marked q D b R :=
  ⟨lift q D b R x, by
    change (markPolynomial q R).eval₂ (Int.castRingHom ℝ) (lift q D b R x).val = 0
    rw [eval_mark, oldBase_lift]
    exact (BoundedZeroSource.sectionMap q R x).property⟩

theorem markedProjection_lift (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (x : Bounded q R) :
    markedProjection q D b R (markedLift q D b R x) = x := by
  have he : oldPoint q D b R (markedLift q D b R x) = BoundedZeroSource.sectionMap q R x := by
    apply Subtype.ext
    change (oldBase q D b R (lift q D b R x)).val = (BoundedZeroSource.sectionMap q R x).val
    exact congrArg (fun w : CircleSublevelLift.Base (scaledEnergy q D b R) (level n D b R) => w.val) (oldBase_lift q D b R x)
  change BoundedZeroSource.projection q R (oldPoint q D b R (markedLift q D b R x)) = x
  rw [he, BoundedZeroSource.projection_section]

noncomputable def oldToBase (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (w : BoundedZeroSource.Zeros q R) :
    CircleSublevelLift.Base (scaledEnergy q D b R) (level n D b R) :=
  ⟨w.val, zero_in_scaled_sublevel q D b R w⟩

theorem continuous_oldToBase (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) : Continuous (oldToBase q D b R) :=
  continuous_subtype_val.subtype_mk _

/-- This attachment stays inside the regular source and only changes slack
coordinates over an original zero. It uses no paths in a positive sublevel
to infer paths in the original singular zero set. -/
theorem joined_to_lift (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (z : Marked q D b R) :
    Joined z.val (lift q D b R (markedProjection q D b R z)) := by
  have ho : Joined (oldPoint q D b R z) (BoundedZeroSource.sectionMap q R (markedProjection q D b R z)) := by
    apply (BoundedZeroSource.joined_iff q R _ _).mpr
    rw [BoundedZeroSource.projection_section]
    exact Joined.refl _
  apply (joined_homeomorph_iff (levelHomeomorph q D b R) _ _).mp
  apply (PurePowerSublevelLift.joined_iff (powerHalfDegree D) (powerHalfDegree_odd D)
    (scaledEnergy q D b R) (continuous_scaledEnergy q D b R) (level n D b R) _ _).mpr
  change Joined (oldBase q D b R z.val) (oldBase q D b R (lift q D b R (markedProjection q D b R z)))
  rw [oldBase_lift]
  exact ho.map (continuous_oldToBase q D b R)

theorem marked_component_iff (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b) (z v : Marked q D b R) :
    v.val ∈ connectedComponent z.val ↔ (markedProjection q D b R v).val ∈
      connectedComponentIn (Bounded q R) (markedProjection q D b R z).val := by
  have hz := connectedComponent_eq (pathComponent_subset_component z.val (joined_to_lift q D b R z))
  have hv := connectedComponent_eq (pathComponent_subset_component v.val (joined_to_lift q D b R v))
  calc
    _ ↔ connectedComponent v.val = connectedComponent z.val := connectedComponent_eq_iff_mem.symm
    _ ↔ connectedComponent (lift q D b R (markedProjection q D b R v)) =
        connectedComponent (lift q D b R (markedProjection q D b R z)) := by rw [hz, hv]
    _ ↔ lift q D b R (markedProjection q D b R v) ∈
        connectedComponent (lift q D b R (markedProjection q D b R z)) := connectedComponent_eq_iff_mem
    _ ↔ _ := (component_iff_lift q D b R hD hb _ _).symm

theorem preconnected_iff_marked (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b) :
    IsPreconnected (Bounded q R) ↔ ∀ z v : Marked q D b R, v.val ∈ connectedComponent z.val := by
  constructor
  · intro h z v
    apply (marked_component_iff q D b R hD hb z v).mpr
    rw [h.connectedComponentIn (markedProjection q D b R z).property]
    exact (markedProjection q D b R v).property
  · intro h
    by_cases hn : (Bounded q R).Nonempty
    · obtain ⟨x, hx⟩ := hn
      have he : connectedComponentIn (Bounded q R) x = Bounded q R := by
        apply (connectedComponentIn_subset _ _).antisymm
        intro y hy
        have hm := (marked_component_iff q D b R hD hb
          (markedLift q D b R ⟨x, hx⟩) (markedLift q D b R ⟨y, hy⟩)).mp (h _ _)
        simpa only [markedProjection_lift] using hm
      rw [← he]
      exact isPreconnected_connectedComponentIn
    · rw [Set.not_nonempty_iff_eq_empty.mp hn]
      exact isPreconnected_empty

end LeanCanny.Geometry.BoundedRegularSource
