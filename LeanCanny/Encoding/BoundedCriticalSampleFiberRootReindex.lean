/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberRoot

/-! # Ordered child roots under attached metadata at actual samples

The parent descriptor and original query record stay fixed while a new
record is attached. Counts and real coordinates agree at every valid ordinal.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberRoot
open LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open BoundedAlgebraicSlice (Family)
open BoundedCriticalSampleSlice
open scoped Classical

theorem roots_attach (P : Readers) (F : Family) (u record : List Bool) :
    RootCount.roots P (F.comp dropRecord) (attach u record) = RootCount.roots P F u := by
  rw [RootCount.roots, RootCount.roots, specialized_attach]

theorem count_attach (P : Readers) (F : Family) (u record : List Bool) :
    RootCount.count P (F.comp dropRecord) (attach u record) = RootCount.count P F u :=
  congrArg Finset.card (roots_attach P F u record)

theorem root_value_attach (P : Readers) (F : Family) (u record : List Bool)
    (r : Fin (RootCount.count P (F.comp dropRecord) (attach u record)))
    (s : Fin (RootCount.count P F u)) (hrs : r.val = s.val) :
    (root P (F.comp dropRecord) (attach u record) r).val = (root P F u s).val := by
  unfold root
  unfold RootCount.count at r s ⊢
  simp only [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply]
  simp only [roots_attach, Fin.getElem_fin, hrs]

end LeanCanny.Encoding.BoundedCriticalSampleFiberRoot
