/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.BoundedMarkedComponents

/-! # Original coordinates of marked regular-source points

The marked projection retains exactly the first original coordinates. This
identifies endpoint fibers directly from their coordinate formulas.
-/

@[expose] public section
namespace LeanCanny.Geometry
open MvPolynomial

theorem BoundedZeroSource.projection_apply {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (R : ℕ)
    (w : BoundedZeroSource.Zeros q R) (i : Fin n) :
    (BoundedZeroSource.projection q R w).val i = w.val (i.castAdd 2) := by
  change (BoundedZeroSource.coordinates.symm w.val).1 i = w.val (i.castAdd 2)
  have h := congrArg (fun x : Fin (n + 2) → ℝ => x (i.castAdd 2))
    (BoundedZeroSource.coordinates.apply_symm_apply w.val)
  simpa only [BoundedZeroSource.coordinates_apply, Fin.append_left] using h

theorem BoundedRegularSource.markedProjection_apply {n : ℕ} (q : MvPolynomial (Fin n) ℤ)
    (D b R : ℕ) (z : BoundedRegularSource.Marked q D b R) (i : Fin n) :
    (BoundedRegularSource.markedProjection q D b R z).val i = z.val.val (i.castAdd 4) := by
  rw [BoundedRegularSource.markedProjection, BoundedZeroSource.projection_apply]
  change (BoundedRegularSource.oldBase q D b R z.val).val (i.castAdd 2) = z.val.val (i.castAdd 4)
  rw [BoundedRegularSource.oldBase_apply]
  rfl

end LeanCanny.Geometry
