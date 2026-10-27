/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.AlgebraicSliceCellCover

/-! # Exact factor signs on every constructed real cell

Point cells use evaluation at their root. Gaps use a one-sided endpoint
sign, except that the unique gap of an empty root set uses evaluation at
zero. These rules include both exterior rays and vanishing factors.
-/

@[expose] public section
namespace LeanCanny.Connectivity.AlgebraicSliceCellSignGeometry
open Set LeanCanny.Algebra LeanCanny.Encoding
open BoundedFullWriter BoundedAlgebraicSlice AlgebraicSliceCellCover Geometry.OrderedRealCells
open scoped Classical

theorem factor_constant (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (i : Fin (Q.count (pairFst u))) (c : AlgebraicSliceCellCover.Index P Q u) (x y : ℝ)
    (hx : x ∈ AlgebraicSliceCellCover.piece P Q u c) (hy : y ∈ AlgebraicSliceCellCover.piece P Q u c) :
    SignType.sign ((BoundedAlgebraicSliceIndexed.value P Q u i.val).eval x) =
      SignType.sign ((BoundedAlgebraicSliceIndexed.value P Q u i.val).eval y) :=
  congrFun (sign_constant P Q u hu c x hx y hy) i

noncomputable def sign (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool)
    (i : ℕ) : AlgebraicSliceCellCover.Index P Q u → SignType
  | .inl r => SignType.sign ((BoundedAlgebraicSliceIndexed.value P Q u i).eval (root (roots P Q u) r))
  | .inr k => if hn : (roots P Q u).card = 0 then
      SignType.sign ((BoundedAlgebraicSliceIndexed.value P Q u i).eval 0)
    else if hk : k.val = 0 then
      PolynomialLocalSign.left (BoundedAlgebraicSliceIndexed.value P Q u i) (root (roots P Q u) ⟨0, by omega⟩)
    else PolynomialLocalSign.right (BoundedAlgebraicSliceIndexed.value P Q u i)
      (root (roots P Q u) ⟨k.val - 1, by have := k.isLt; omega⟩)

theorem gap_zero_sign (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (i : Fin (Q.count (pairFst u))) (hn : 0 < (roots P Q u).card) (y : ℝ)
    (hy : y ∈ gap (roots P Q u) ⟨0, by omega⟩) :
    SignType.sign ((BoundedAlgebraicSliceIndexed.value P Q u i.val).eval y) =
      PolynomialLocalSign.left (BoundedAlgebraicSliceIndexed.value P Q u i.val) (root (roots P Q u) ⟨0, hn⟩) := by
  obtain ⟨δ, hδ, H⟩ := PolynomialLocalSign.left_eventually (BoundedAlgebraicSliceIndexed.value P Q u i.val)
    (root (roots P Q u) ⟨0, hn⟩)
  have hz : root (roots P Q u) ⟨0, hn⟩ - δ / 2 ∈ gap (roots P Q u) ⟨0, by omega⟩ := by
    rw [gap_zero hn]
    change _ < _
    linarith
  exact (factor_constant P Q u hu i (.inr ⟨0, by omega⟩) y _ hy hz).trans
    (H (δ / 2) (by linarith) (by linarith))

theorem gap_positive_sign (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (i : Fin (Q.count (pairFst u))) (k : Fin ((roots P Q u).card + 1)) (hk : 0 < k.val) (y : ℝ)
    (hy : y ∈ gap (roots P Q u) k) :
    SignType.sign ((BoundedAlgebraicSliceIndexed.value P Q u i.val).eval y) =
      PolynomialLocalSign.right (BoundedAlgebraicSliceIndexed.value P Q u i.val)
        (root (roots P Q u) ⟨k.val - 1, by have := k.isLt; omega⟩) := by
  let r : Fin (roots P Q u).card := ⟨k.val - 1, by have := k.isLt; omega⟩
  let a := root (roots P Q u) r
  have hay : a < y := by
    have H := (mem_gap_iff _ k y).mp hy r
    simpa only [r, show k.val - 1 < k.val from by omega, ite_true] using H
  obtain ⟨δ, hδ, H⟩ := PolynomialLocalSign.right_eventually (BoundedAlgebraicSliceIndexed.value P Q u i.val) a
  let ε := min δ (y - a) / 2
  have hε : 0 < ε := div_pos (lt_min hδ (sub_pos.mpr hay)) (by norm_num)
  have hεδ : ε < δ := by have := min_le_left δ (y - a); dsimp [ε]; linarith
  have hεy : a + ε < y := by have := min_le_right δ (y - a); dsimp [ε]; linarith
  have hz : a + ε ∈ gap (roots P Q u) k := by
    rw [mem_gap_iff]
    intro j
    have hyj := (mem_gap_iff _ k y).mp hy j
    split_ifs with hj
    · have hja : root (roots P Q u) j ≤ a := (root_strictMono _).monotone
        (show j ≤ r from by change j.val ≤ k.val - 1; omega)
      linarith
    · rw [ite_eq_right hj] at hyj
      exact hεy.trans hyj
  exact (factor_constant P Q u hu i (.inr k) y _ hy hz).trans (H ε hε hεδ)

theorem packet (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (i : Fin (Q.count (pairFst u))) (c : AlgebraicSliceCellCover.Index P Q u) (y : ℝ)
    (hy : y ∈ AlgebraicSliceCellCover.piece P Q u c) :
    sign P Q u i.val c = SignType.sign ((BoundedAlgebraicSliceIndexed.value P Q u i.val).eval y) := by
  cases c with
  | inl r =>
    change y = root (roots P Q u) r at hy
    rw [sign, hy]
  | inr k =>
    change y ∈ gap (roots P Q u) k at hy
    by_cases hn : (roots P Q u).card = 0
    · rw [sign, dite_eq_left hn]
      have hz : (0 : ℝ) ∈ gap (roots P Q u) k := by
        rw [mem_gap_iff]
        intro j
        have := j.isLt
        omega
      exact factor_constant P Q u hu i (.inr k) 0 y hz hy
    · rw [sign, dite_eq_right hn]
      by_cases hk : k.val = 0
      · rw [dite_eq_left hk]
        have he : k = ⟨0, by omega⟩ := Fin.ext hk
        have hy0 : y ∈ gap (roots P Q u) ⟨0, by omega⟩ := he ▸ hy
        exact (gap_zero_sign P Q u hu i (by omega) y hy0).symm
      · rw [dite_eq_right hk]
        exact (gap_positive_sign P Q u hu i k (by omega) y hy).symm

end LeanCanny.Connectivity.AlgebraicSliceCellSignGeometry
