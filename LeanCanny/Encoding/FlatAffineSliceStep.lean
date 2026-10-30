/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSlicePresentation

/-! # Adding one coordinate equation to an affine slice -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSlicePresentation
open scoped BigOperators Classical

theorem coordinate_sum {n : ℕ} (r : Fin n) (y : Fin n → ℝ) :
    (∑ i, ((2 * LeanCanny.Algebra.FermatCoordinateCone.normal r i : ℤ) : ℝ) * y i) = 2 * y r := by
  simp [LeanCanny.Algebra.FermatCoordinateCone.normal, ite_mul]

theorem set_step {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (s t : Finset (Fin n))
    (r : Fin n) (a c : Fin n → Fin n → ℤ) (b d : Fin n → ℝ) (v : ℝ)
    (hs : s = insert r t) (ha : a = c) (hb : ∀ j ∈ t, b j = d j)
    (hr : ∀ y : Fin n → ℝ, (∑ i, (a r i : ℝ) * y i) = 2 * y r) (hv : b r = v) :
    set p s a b = {y | y ∈ set p t c d ∧ 2 * y r = v} := by
  subst s
  subst c
  ext y
  simp only [set, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hp, hl⟩
    refine ⟨⟨hp, fun j hj => ?_⟩, ?_⟩
    · exact (hl j (Finset.mem_insert_of_mem hj)).trans (hb j hj)
    · exact (hr y).symm.trans ((hl r (Finset.mem_insert_self _ _)).trans hv)
  · rintro ⟨⟨hp, hl⟩, hy⟩
    refine ⟨hp, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with he | hj
    · subst j
      exact (hr y).trans (hy.trans hv.symm)
    · exact (hl j hj).trans (hb j hj).symm

theorem step_transport {α : Type*} (A S B : Set α) (f : α → Prop)
    (hA : A = {y | y ∈ S ∧ f y}) (hS : S = B) : A = {y | y ∈ B ∧ f y} := by
  subst B
  exact hA

end LeanCanny.Encoding.FlatAffineSlicePresentation
