/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.PositiveMarginValues
/-! # Total natural-index margin values shield the native metadata behind generic bounds -/
@[expose] public section
namespace LeanCanny.Connectivity.PositiveMarginValues
open ETR LeanCanny.Encoding MonotoneGateSource
open scoped Classical

noncomputable def natValue (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) (i : ℕ) : ℝ :=
  if hi : i < F.count c then value F c x ⟨i,hi⟩ else 0

theorem natValue_valid (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) (i : ℕ) (hi : i < F.count c) :
    natValue F c x i=value F c x ⟨i,hi⟩ := by
  unfold natValue
  rw [dite_eq_left hi]

theorem child_natValue (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) (i : Fin (F.count c))
    (j : ℕ) (hj : j < i.val) : childValue F c x i j=natValue F c x j := by
  unfold childValue natValue
  rw [dite_eq_left hj,dite_eq_left (hj.trans i.isLt)]

end LeanCanny.Connectivity.PositiveMarginValues
