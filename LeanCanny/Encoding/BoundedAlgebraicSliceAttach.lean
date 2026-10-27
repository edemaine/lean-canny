/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceReindex

/-! # Attaching records to arbitrary raw algebraic-root queries

The total query interface preserves the base point and its validity even
for redundant binary ordinals and malformed surrounding packet words.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice
open LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open scoped Classical
attribute [local irreducible] BoundedProjectionRootCount.count BoundedProjectionOrderedRoot.root

theorem valid_attach (P : Readers) (u record : List Bool) :
    signQuery (pair u record) ∈ valid (P.comp pairFst) ↔ u ∈ valid P := by
  simp only [valid, Set.mem_ofPred_eq, signQuery, pairFst_pair, pairSnd_pair,
    BoundedProjectionRootCount.count_comp, BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits]

theorem specialized_attach_raw (P : Readers) (G : Family) (u record : List Bool) :
    specialized (P.comp pairFst) G (signQuery (pair u record)) =
      if u ∈ valid P then G.slice (pair (pairFst u) record) (point P u) else 0 := by
  by_cases hu : u ∈ valid P
  · rw [ite_eq_left hu]
    let c := pairFst u
    let r : Fin (BoundedProjectionRootCount.count P c) := ⟨Nat.fromBitsLE (pairSnd u), hu⟩
    have hq : signQuery (pair u record) = signQuery (pair (pair c (BinaryNatCode.encode r.val)) record) := by
      simp only [signQuery, c, r, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have hp : point P u = (BoundedProjectionOrderedRoot.root P c r).val := by
      rw [point, dite_eq_left hu]
    rw [hq, specialized_attach, hp]
  · have hv : signQuery (pair u record) ∉ valid (P.comp pairFst) := fun h => hu ((valid_attach P u record).mp h)
    rw [specialized, ite_eq_right hv, ite_eq_right hu]

theorem specialized_attach_comp (P : Readers) (F : Family) (u record : List Bool) :
    specialized (P.comp pairFst) (F.comp pairFst) (signQuery (pair u record)) = specialized P F u := by
  rw [specialized_attach_raw]
  by_cases hu : u ∈ valid P
  · rw [ite_eq_left hu, specialized, ite_eq_left hu, Family.slice_comp, pairFst_pair]
  · rw [ite_eq_right hu, specialized, ite_eq_right hu]

end LeanCanny.Encoding.BoundedAlgebraicSlice
