/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.OrderedRealCellNeighborhood
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Algebraic samples in bounded polynomial root gaps

Rolle's theorem supplies a derivative root in every interior retained gap.
This gives algebraic sample candidates without writing isolating rationals.
The original polynomial need not be squarefree.
-/

@[expose] public section
namespace LeanCanny.Geometry.OrderedRealCells
open Set
open scoped Classical

theorem rightGap_eq_Ioo (s : Finset ℝ) (i : Fin s.card) (hi : i.val + 1 < s.card) :
    gap s (rightGap s i) = Ioo (root s i) (root s ⟨i.val + 1, hi⟩) := by
  have H := gap_interior (rightGap s i) (by change 0 < i.val + 1; omega) hi
  simpa only [rightGap, Nat.add_sub_cancel, Fin.eta] using H

theorem leftGap_eq_Ioo (s : Finset ℝ) (i : Fin s.card) (hi : 0 < i.val) :
    gap s (leftGap s i) = Ioo (root s ⟨i.val - 1, by have := i.isLt; omega⟩) (root s i) := by
  exact gap_interior (leftGap s i) hi i.isLt

theorem exists_derivative_in_gap (p : Polynomial ℝ) (s : Finset ℝ)
    (hs : ∀ t ∈ s, p.eval t = 0) (k : Fin (s.card + 1)) (h0 : 0 < k.val) (hk : k.val < s.card) :
    ∃ t ∈ gap s k, p.derivative.eval t = 0 := by
  have hab : root s ⟨k.val - 1, by omega⟩ < root s ⟨k.val, hk⟩ :=
    root_strictMono s (by change k.val - 1 < k.val; omega)
  obtain ⟨t, ht, hp⟩ := exists_hasDerivAt_eq_zero hab
    (fun t _ => (p.hasDerivAt t).continuousAt.continuousWithinAt)
    ((hs _ (root_mem s _)).trans (hs _ (root_mem s _)).symm) (fun t _ => p.hasDerivAt t)
  exact ⟨t, (gap_interior k h0 hk).symm ▸ ht, hp⟩

theorem rightGap_lt_root (s : Finset ℝ) (i j : Fin s.card) (hij : root s i < root s j)
    {t : ℝ} (ht : t ∈ gap s (rightGap s i)) : t < root s j := by
  have hij' : i < j := (root_strictMono s).lt_iff_lt.mp hij
  have hj : ¬j.val < (rightGap s i).val := by change ¬j.val < i.val + 1; change i.val < j.val at hij'; omega
  simpa only [hj, ite_false] using (mem_gap_iff s (rightGap s i) t).mp ht j

theorem root_lt_leftGap (s : Finset ℝ) (i j : Fin s.card) (hij : root s j < root s i)
    {t : ℝ} (ht : t ∈ gap s (leftGap s i)) : root s j < t := by
  have hj : j.val < (leftGap s i).val := (root_strictMono s).lt_iff_lt.mp hij
  simpa only [hj, ite_true] using (mem_gap_iff s (leftGap s i) t).mp ht j

theorem exists_derivative_rightGap (p : Polynomial ℝ) (s : Finset ℝ) (hs : ∀ t ∈ s, p.eval t = 0)
    (i j : Fin s.card) (hij : root s i < root s j) :
    ∃ t ∈ gap s (rightGap s i), t < root s j ∧ p.derivative.eval t = 0 := by
  have hij' : i < j := (root_strictMono s).lt_iff_lt.mp hij
  obtain ⟨t, ht, hp⟩ := exists_derivative_in_gap p s hs (rightGap s i)
    (by change 0 < i.val + 1; omega) (by change i.val + 1 < s.card; have := j.isLt; change i.val < j.val at hij'; omega)
  exact ⟨t, ht, rightGap_lt_root s i j hij ht, hp⟩

theorem exists_derivative_leftGap (p : Polynomial ℝ) (s : Finset ℝ) (hs : ∀ t ∈ s, p.eval t = 0)
    (i j : Fin s.card) (hij : root s j < root s i) :
    ∃ t ∈ gap s (leftGap s i), root s j < t ∧ p.derivative.eval t = 0 := by
  have hij' : j < i := (root_strictMono s).lt_iff_lt.mp hij
  obtain ⟨t, ht, hp⟩ := exists_derivative_in_gap p s hs (leftGap s i)
    (by change 0 < i.val; change j.val < i.val at hij'; omega) i.isLt
  exact ⟨t, ht, root_lt_leftGap s i j hij ht, hp⟩

end LeanCanny.Geometry.OrderedRealCells
