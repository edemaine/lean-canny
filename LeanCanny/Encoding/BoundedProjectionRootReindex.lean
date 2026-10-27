/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionOrderedRoot

/-! # Ordered root labels under context reindexing

Adding query metadata to a context preserves the underlying ordered roots.
The hash and basis searches may be recomputed, but the decoded real root is
determined by the polynomial and its real-order index.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionRootCount
open LeanCanny.ETR BoundedFullWriter

theorem count_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool) :
    count (P.comp f) c = count P (f c) := congrArg Finset.card (rootSet_comp P f c)

end LeanCanny.Encoding.BoundedProjectionRootCount

namespace LeanCanny.Encoding.BoundedProjectionOrderedRoot
open LeanCanny.ETR BoundedFullWriter
open scoped Classical

theorem root_value_context (P : Readers) (c d : List Bool) (hcd : c = d)
    (r : Fin (BoundedProjectionRootCount.count P c)) (s : Fin (BoundedProjectionRootCount.count P d))
    (hrs : r.val = s.val) : (root P c r).val = (root P d s).val := by
  subst d
  exact congrArg (fun i => (root P c i).val) (Fin.ext hrs)

theorem root_value_reindex (P : Readers) (f : List Bool → List Bool) (c d : List Bool) (hcd : f c = d)
    (r : Fin (BoundedProjectionRootCount.count (P.comp f) c)) (s : Fin (BoundedProjectionRootCount.count P d))
    (hrs : r.val = s.val) : (root (P.comp f) c r).val = (root P d s).val := by
  rw [root_eq_ordered, root_eq_ordered]
  unfold BoundedProjectionRootCount.count at r s ⊢
  simp only [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply]
  simp only [BoundedProjectionRootCount.rootSet_comp, hcd]
  simp only [Fin.getElem_fin, hrs]

theorem root_value_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool)
    (r : Fin (BoundedProjectionRootCount.count (P.comp f) c)) (s : Fin (BoundedProjectionRootCount.count P (f c)))
    (hrs : r.val = s.val) : (root (P.comp f) c r).val = (root P (f c) s).val :=
  root_value_reindex P f c (f c) rfl r s hrs

end LeanCanny.Encoding.BoundedProjectionOrderedRoot
