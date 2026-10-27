/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceAttach

/-! # The base point is unchanged by attached query metadata -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice
open LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open scoped Classical

theorem point_attach (P : Readers) (u record : List Bool) :
    point (P.comp pairFst) (signQuery (pair u record)) = point P u := by
  let v := signQuery (pair u record)
  by_cases hu : u ∈ valid P
  · have hv : v ∈ valid (P.comp pairFst) := (valid_attach P u record).mpr hu
    let r : Fin (BoundedProjectionRootCount.count (P.comp pairFst) (pairFst v)) :=
      ⟨Nat.fromBitsLE (pairSnd v), hv⟩
    let s : Fin (BoundedProjectionRootCount.count P (pairFst u)) := ⟨Nat.fromBitsLE (pairSnd u), hu⟩
    have hc : pairFst (pairFst v) = pairFst u := by simp only [v, signQuery, pairFst_pair]
    have hi : r.val = s.val := by
      simp only [r, s, v, signQuery, pairSnd_pair, pairFst_pair, BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits]
    have H := BoundedProjectionOrderedRoot.root_value_reindex P pairFst (pairFst v) (pairFst u) hc r s hi
    change point (P.comp pairFst) v = point P u
    rw [point, dite_eq_left hv, point, dite_eq_left hu]
    exact H
  · have hv : v ∉ valid (P.comp pairFst) := fun h => hu ((valid_attach P u record).mp h)
    change point (P.comp pairFst) v = point P u
    rw [point, dite_eq_right hv, point, dite_eq_right hu]

end LeanCanny.Encoding.BoundedAlgebraicSlice
