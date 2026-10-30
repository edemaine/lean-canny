/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveValueGramSpace

/-! # Computed binary metadata for uniform coordinate-grid value certificates

The Macaulay level is (e-1) + n*(D-1) + 1. Dimension is unary; both degree
allowances remain binary. The canonical exponent width is computed from the
level, and every original row-degree request uses the supplied native bounds.
-/

@[expose] public section
namespace LeanCanny.Algebra.ProjectiveValueGramBits
open LeanCanny.Encoding LeanCanny.Computation
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

theorem Family.uniform_controls (F : Family) (D : List Bool → ℕ)
    (hn : UnaryFn F.arity) (hD : BinaryFn D) (he : BinaryFn F.testDegree)
    (hd : ∀ c i, F.degree c i = D c)
    (hw : ∀ c, F.width c = (F.layout.level c).size) : F.layout.Controls := by
  have hl : BinaryFn F.layout.level := by
    apply (((he.sub (BinaryFn.const 1)).add
      ((BinaryFn.ofUnary hn).mul (hD.sub (BinaryFn.const 1)))).add (BinaryFn.const 1)).of_eq
    intro c
    simp only [Family.layout, Macaulay.level, ProjectiveValueGram.degrees, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hwidth : UnaryFn F.width := (UnaryFn.length hl.bits_mem_FP).of_eq (fun c =>
    (Nat.size_eq_bits_len _).trans (hw c).symm)
  refine ⟨hn.add (UnaryFn.const 1), hwidth, hl, ?_⟩
  have hz := (BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)
  exact (BinaryFn.ite hz (he.comp pairFst_mem_FP) (hD.comp pairFst_mem_FP)).of_eq (fun q => by
    simp only [Function.comp_apply, Family.layout, hd])

end LeanCanny.Algebra.ProjectiveValueGramBits
