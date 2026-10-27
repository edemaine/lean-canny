/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberRoot
public import LeanCanny.Encoding.BoundedAlgebraicSliceAttach

/-! # Ordered fiber roots under attached query metadata

Attaching a native query record preserves the specialized root polynomial,
its distinct-root count, and the real coordinate at every valid ordinal.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberRoot
open LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter BoundedAlgebraicSlice
open scoped Classical

theorem roots_attach (P : Readers) (F : Family) (u record : List Bool) :
    RootCount.roots (P.comp pairFst) (F.comp pairFst) (signQuery (pair u record)) =
      RootCount.roots P F u := by
  rw [RootCount.roots, RootCount.roots, specialized_attach_comp]

theorem count_attach (P : Readers) (F : Family) (u record : List Bool) :
    RootCount.count (P.comp pairFst) (F.comp pairFst) (signQuery (pair u record)) = RootCount.count P F u :=
  congrArg Finset.card (roots_attach P F u record)

theorem root_value_attach (P : Readers) (F : Family) (u record : List Bool)
    (r : Fin (RootCount.count (P.comp pairFst) (F.comp pairFst) (signQuery (pair u record))))
    (s : Fin (RootCount.count P F u)) (hrs : r.val = s.val) :
    (root (P.comp pairFst) (F.comp pairFst) (signQuery (pair u record)) r).val = (root P F u s).val := by
  unfold root
  unfold RootCount.count at r s ⊢
  simp only [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply]
  simp only [roots_attach, Fin.getElem_fin, hrs]

end LeanCanny.Encoding.BoundedAlgebraicFiberRoot
