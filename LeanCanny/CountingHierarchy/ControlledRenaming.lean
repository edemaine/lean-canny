/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled

/-! # Controlled variable renaming through native coordinate readers -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

/-- A polynomial-time coordinate reader realizes a variable renaming. This
supports padding, reordering, and inserting auxiliary-variable blocks while
preserving the evaluation level and the original degree and mass budgets. -/
noncomputable def rename {α : Type} {n m : α → ℕ}
    {P : (w : α) → MvPolynomial (Fin (n w)) ℤ} {enc : α ↪ List Bool} {a : ℕ}
    (C : Controlled P enc a) (hm : ComputableInPolyTime m enc encUnary)
    (f : (w : α) → Fin (n w) → Fin (m w)) (read : α × List ℕ → List ℕ)
    (hread : ComputableInPolyTime read (encPair enc (encList encNat)) (encList encNat))
    (hcoords : ∀ w z (i : Fin (n w)), (read (w, z))[i.val]?.getD 0 = z[(f w i).val]?.getD 0) :
    Controlled (fun w => MvPolynomial.rename (f w) (P w)) enc a where
  arity_computable := hm
  degreeBound := C.degreeBound
  degree_computable := C.degree_computable
  degree_le w := (totalDegree_rename_le _ _).trans (C.degree_le w)
  massExponent := C.massExponent
  mass_computable := C.mass_computable
  mass_le w := (LeanCanny.Algebra.MvMass.rename_le _ _).trans (C.mass_le w)
  cutoff := C.cutoff
  cutoff_computable := C.cutoff_computable
  evaluate q := C.evaluate (q.1, q.2.1, read (q.1, q.2.2))
  evaluate_mem := by
    have hf : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.1)
        (encEvaluation enc) enc := .fst _ _
    have hp : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.1)
        (encEvaluation enc) encNat := (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)
    have hz : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.2)
        (encEvaluation enc) (encList encNat) := (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)
    exact CountingFunction.preprocess C.evaluate_mem (hf.prod (hp.prod (hread.comp (hf.prod hz))))
  evaluate_eq w p z hp hcut := by
    rw [C.evaluate_eq w p (read (w, z)) hp hcut]
    unfold evaluation
    rw [MvPolynomial.eval₂_rename]
    congr 2
    funext i
    rw [hcoords]
    rfl

end LeanCanny.CountingHierarchy.Controlled
