/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixMinorSection
public import Mathlib.LinearAlgebra.Matrix.Block

/-! # Splitting a contraction determinant along selected rows

If the relation matrix vanishes on the selected rows, the source contraction
is block triangular. Its diagonal blocks are the selected multiplication
matrix and the complementary principal relation matrix.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixSelectedBlock
open scoped Matrix Classical
variable {R S T : Type*} [CommRing R] [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

omit [Fintype S] [DecidableEq T] in
theorem mul_rowSelection_not_mem (D : Matrix S T R) (f : T → S) (a b : S) (hb : b ∉ Set.range f) :
    (D * MatrixMinorSection.rowSelection (R := R) f) a b = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t _
  have htb : f t ≠ b := fun h => hb ⟨t, h⟩
  change D a t * (1 : Matrix S S R) (f t) b = 0
  rw [Matrix.one_apply, ite_eq_right htb, mul_zero]

omit [Fintype S] in
theorem mul_rowSelection_submatrix (D : Matrix S T R) (f : T → S) (hf : Function.Injective f) :
    (D * MatrixMinorSection.rowSelection (R := R) f).submatrix f f = D.submatrix f id := by
  funext a b
  change (∑ t, D (f a) t * (1 : Matrix S S R) (f t) (f b)) = D (f a) b
  simp only [Matrix.one_apply, hf.eq_iff, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem determinant (D : Matrix S T R) (E : Matrix S S R) (f : T → S) (hf : Function.Injective f)
    (hE : ∀ t, E (f t) = 0) :
    (D * MatrixMinorSection.rowSelection (R := R) f + E).det = (D.submatrix f id).det *
      (E.submatrix (fun a : {a : S // a ∉ Set.range f} => a.val) (fun a => a.val)).det := by
  -- Match the subtype enumeration used by the two-block determinant theorem.
  let : Fintype (Set.range f) := Subtype.fintype (fun a : S => a ∈ Set.range f)
  let A := D * MatrixMinorSection.rowSelection (R := R) f + E
  have hu (a : S) (ha : a ∈ Set.range f) (b : S) (hb : b ∉ Set.range f) : A a b = 0 := by
    obtain ⟨t, rfl⟩ := ha
    change (D * MatrixMinorSection.rowSelection (R := R) f) (f t) b + E (f t) b = 0
    rw [mul_rowSelection_not_mem D f _ _ hb, hE t, Pi.zero_apply, add_zero]
  have hdet := Matrix.twoBlockTriangular_det' A (fun a => a ∈ Set.range f) hu
  have hfirst : (Matrix.toSquareBlockProp A (fun a => a ∈ Set.range f)).det = (D.submatrix f id).det := by
    rw [← Matrix.det_submatrix_equiv_self (Equiv.ofInjective f hf)]
    apply congrArg Matrix.det
    funext a b
    change (D * MatrixMinorSection.rowSelection (R := R) f) (f a) (f b) + E (f a) (f b) = D (f a) b
    rw [hE a, Pi.zero_apply, add_zero]
    exact congrFun (congrFun (mul_rowSelection_submatrix D f hf) a) b
  have hsecond : Matrix.toSquareBlockProp A (fun a => a ∉ Set.range f) =
      E.submatrix (fun a : {a : S // a ∉ Set.range f} => a.val) (fun a => a.val) := by
    funext a b
    change (D * MatrixMinorSection.rowSelection (R := R) f) a.val b.val + E a.val b.val = E a.val b.val
    rw [mul_rowSelection_not_mem D f _ _ b.property, zero_add]
  exact hdet.trans (congrArg₂ (· * ·) hfirst (congrArg Matrix.det hsecond))

end LeanCanny.Algebra.MatrixSelectedBlock
