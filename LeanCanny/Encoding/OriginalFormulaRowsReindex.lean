/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.OriginalFormulaRowsBinary
/-! # Native root/context reindexing of original polynomial rows -/
@[expose] public section
namespace LeanCanny.Encoding.OriginalFormulaRows
open ETR LeanCanny.Computation

def Family.comp (F : Family) (read : List Bool → List Bool) : Family where
  arity c := F.arity (read c)
  count c := F.count (read c)
  degree c := F.degree (read c)
  mass c := F.mass (read c)
  term q := F.term (pair (read (pairFst q)) (pairSnd q))
  term_scope q := by simpa only [pairFst_pair] using F.term_scope (pair (read (pairFst q)) (pairSnd q))
  degree_bound c i := by simpa only [pairFst_pair,pairSnd_pair] using F.degree_bound (read c) i
  mass_bound c i := by simpa only [pairFst_pair,pairSnd_pair] using F.mass_bound (read c) i

theorem Family.Access.comp {F : Family} (A : F.Access) (read : List Bool → List Bool) (hr : read ∈ FP) :
    (F.comp read).Access := by
  have HQ := mem_FP_pair (mem_FP_comp (f := pairFst) (g := read) pairFst_mem_FP hr) pairSnd_mem_FP
  exact ⟨A.arity.comp hr,A.count.comp hr,A.degree.comp hr,A.mass.comp hr,
    mem_FP_comp (f := fun q => pair (read (pairFst q)) (pairSnd q))
      (g := fun q => (F.term q).toData.toBits) HQ A.term⟩

theorem Family.polynomial_comp (F : Family) (read : List Bool → List Bool) (c : List Bool) (i : ℕ) :
    (F.comp read).polynomial c i=F.polynomial (read c) i := by
  simp only [Family.polynomial,Family.comp,pairFst_pair,pairSnd_pair]

end LeanCanny.Encoding.OriginalFormulaRows
