/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

/-! # A closed algebraic lift of a polynomial degree piece -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Set
open scoped BigOperators Classical

variable {A : Type*} {N : ℕ}

def degreePiece (a : Fin (N + 1) → A → ℝ) (d : Fin (N + 1)) : Set A :=
  {x | a d x ≠ 0 ∧ ∀ j, d.val < j.val → a j x = 0}

noncomputable def degreePieceLiftValue (a : Fin (N + 1) → A → ℝ) (d : Fin (N + 1))
    (z : A × ℝ) : ℝ :=
  (a d z.1 * z.2 - 1) ^ 2 + ∑ j : Fin (N + 1), if d.val < j.val then (a j z.1) ^ 2 else 0

theorem degreePieceLiftValue_nonneg (a : Fin (N + 1) → A → ℝ) (d : Fin (N + 1)) (z : A × ℝ) :
    0 ≤ degreePieceLiftValue a d z := by
  apply add_nonneg (sq_nonneg _)
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

theorem degreePieceLiftValue_eq_zero_iff (a : Fin (N + 1) → A → ℝ) (d : Fin (N + 1)) (z : A × ℝ) :
    degreePieceLiftValue a d z = 0 ↔ a d z.1 * z.2 = 1 ∧ ∀ j, d.val < j.val → a j z.1 = 0 := by
  have hterm (j : Fin (N + 1)) : 0 ≤ if d.val < j.val then (a j z.1) ^ 2 else 0 := by
    split_ifs <;> positivity
  have hsum := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hterm j)
  constructor
  · intro hz
    have hsq : (a d z.1 * z.2 - 1) ^ 2 = 0 := by dsimp only [degreePieceLiftValue] at hz; nlinarith
    refine ⟨by have := sq_eq_zero_iff.mp hsq; linarith, fun j hj => ?_⟩
    have hjle := Finset.single_le_sum (f := fun j : Fin (N + 1) => if d.val < j.val then (a j z.1) ^ 2 else 0)
      (fun j _ => hterm j) (Finset.mem_univ j)
    rw [ite_eq_left hj] at hjle
    dsimp only [degreePieceLiftValue] at hz
    have hjz : (a j z.1) ^ 2 = 0 := by nlinarith [sq_nonneg (a d z.1 * z.2 - 1), sq_nonneg (a j z.1)]
    exact sq_eq_zero_iff.mp hjz
  · rintro ⟨he, hh⟩
    simp only [degreePieceLiftValue, he, sub_self, zero_pow (by decide : 2 ≠ 0), zero_add]
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with hj
    · rw [hh j hj, zero_pow (by decide : 2 ≠ 0)]
    · rfl

variable [TopologicalSpace A]

theorem degreePieceLiftValue_continuous (a : Fin (N + 1) → A → ℝ) (d : Fin (N + 1))
    (ha : ∀ j, Continuous (a j)) : Continuous (degreePieceLiftValue a d) := by
  apply (((ha d).comp continuous_fst).mul continuous_snd |>.sub continuous_const |>.pow 2).add
  apply continuous_finsetSum
  intro j _
  split_ifs
  · exact ((ha j).comp continuous_fst).pow 2
  · exact continuous_const

noncomputable def degreePieceLiftProjection (a : Fin (N + 1) → A → ℝ) (d : Fin (N + 1))
    (z : {z : A × ℝ // degreePieceLiftValue a d z = 0}) : degreePiece a d :=
  ⟨z.val.1, by
    obtain ⟨he, hh⟩ := (degreePieceLiftValue_eq_zero_iff a d z.val).mp z.property
    exact ⟨left_ne_zero_of_mul_eq_one he, hh⟩⟩

noncomputable def degreePieceLiftSection (a : Fin (N + 1) → A → ℝ) (d : Fin (N + 1))
    (x : degreePiece a d) : {z : A × ℝ // degreePieceLiftValue a d z = 0} :=
  ⟨(x.val, (a d x.val)⁻¹), (degreePieceLiftValue_eq_zero_iff a d _).mpr
    ⟨mul_inv_cancel₀ x.property.1, x.property.2⟩⟩

noncomputable def degreePieceLiftEquiv (a : Fin (N + 1) → A → ℝ) (d : Fin (N + 1)) :
    {z : A × ℝ // degreePieceLiftValue a d z = 0} ≃ degreePiece a d where
  toFun := degreePieceLiftProjection a d
  invFun := degreePieceLiftSection a d
  left_inv z := by
    apply Subtype.ext
    change (z.val.1, (a d z.val.1)⁻¹) = z.val
    refine Prod.ext rfl ?_
    obtain ⟨he, _⟩ := (degreePieceLiftValue_eq_zero_iff a d z.val).mp z.property
    have hn := left_ne_zero_of_mul_eq_one he
    apply (mul_left_cancel₀ hn)
    simpa only [mul_inv_cancel₀ hn] using he.symm
  right_inv _ := rfl

noncomputable def degreePieceLiftHomeomorph (a : Fin (N + 1) → A → ℝ) (d : Fin (N + 1))
    (ha : ∀ j, Continuous (a j)) :
    {z : A × ℝ // degreePieceLiftValue a d z = 0} ≃ₜ degreePiece a d where
  toEquiv := degreePieceLiftEquiv a d
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.prodMk
    (((ha d).comp continuous_subtype_val).inv₀ (fun x => x.property.1))).subtype_mk _

/-- Both sides of a relative clopen partition of the lifted zero set are
closed in the ambient parameter-and-inverse space. -/
theorem degreePieceLift_closed_image (a : Fin (N + 1) → A → ℝ) (d : Fin (N + 1))
    (ha : ∀ j, Continuous (a j))
    (C : Set {z : A × ℝ // degreePieceLiftValue a d z = 0}) (hC : IsClopen C) :
    IsClosed (Subtype.val '' C) ∧ IsClosed (Subtype.val '' Cᶜ) := by
  have hZ : IsClosed {z : A × ℝ | degreePieceLiftValue a d z = 0} :=
    isClosed_eq (degreePieceLiftValue_continuous a d ha) continuous_const
  exact ⟨hZ.isClosedEmbedding_subtypeVal.isClosedMap C hC.isClosed,
    hZ.isClosedEmbedding_subtypeVal.isClosedMap Cᶜ hC.compl.isClosed⟩

end LeanCanny.CountingHierarchy
