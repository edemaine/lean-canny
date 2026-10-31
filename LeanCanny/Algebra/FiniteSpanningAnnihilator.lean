/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! # Characteristic annihilators from finite spanning relations

A nonzero evaluation row satisfying the multiplication relations suffices
to annihilate a selected value by a characteristic polynomial. The indexed
monomials need not be an independent basis of the quotient. Specialization
may have a kernel, so coefficient rings with nilpotents are allowed.
-/

@[expose] public section
namespace LeanCanny.Algebra.FiniteSpanningAnnihilator
open Matrix Module
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable {ι R K : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [Field K]

theorem charpoly_root (M : Matrix ι ι R) (φ : R →+* K) (a : K) (v : ι → K)
    (hv : v ≠ 0) (hM : v ᵥ* M.map φ = a • v) : M.charpoly.eval₂ φ a = 0 := by
  have HE : Module.End.HasEigenvector (M.map φ)ᵀ.toLin' a v := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv⟩
    change (M.map φ)ᵀ *ᵥ v = a • v
    rw [Matrix.mulVec_transpose]
    exact hM
  have H := (Module.End.hasEigenvalue_iff_isRoot_charpoly (M.map φ)ᵀ.toLin' a).mp
    (Module.End.hasEigenvalue_of_hasEigenvector HE)
  simpa only [Matrix.charpoly_toLin', Matrix.charpoly_transpose, Matrix.charpoly_map,
    Polynomial.IsRoot, Polynomial.eval_map] using H

theorem charpoly_root_of_relations (M : Matrix ι ι R) (φ : R →+* K) (a : K) (v : ι → K)
    (hv : ∃ i, v i ≠ 0) (hM : ∀ j, ∑ i, v i * φ (M i j) = a * v j) :
    M.charpoly.eval₂ φ a = 0 := by
  apply charpoly_root M φ a v ?_ ?_
  · obtain ⟨i, hi⟩ := hv
    intro H
    exact hi (congrFun H i)
  · funext j
    exact hM j

end LeanCanny.Algebra.FiniteSpanningAnnihilator
