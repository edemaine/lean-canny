/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCriticalStage

/-! # Removing a varied height at a singular critical point

When the objective multiplier is zero, the multiplier of an active height
can become the objective multiplier after that height is removed. The
ambient point and every ancestral coordinate stay fixed. Only the removed
height equation may have a nonzero value in the original system.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineCriticalCoarsening
open MvPolynomial FlatAffineCriticalStage
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {ι R K : Type*} {n : ℕ} [CommRing R] [CommRing K]

def table (a : Fin (n + 1) → Fin n → R) (h : Fin n) : Fin (n + 1) → Fin n → R :=
  Fin.cases (a h.succ) (fun j => a j.succ)

def multipliers (mu : Fin (n + 1) → K) (h : Fin n) : Fin (n + 1) → K :=
  Fin.cases (mu h.succ) (fun j => if j = h then 0 else mu j.succ)

theorem gradient_sum (φ : R →+* K) (a : Fin (n + 1) → Fin n → R)
    (mu : Fin (n + 1) → K) (h : Fin n) (hz : mu 0 = 0) (i : Fin n) :
    (∑ j, φ (table a h j i) * multipliers mu h j) = ∑ j, φ (a j i) * mu j := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [table, multipliers, Fin.cases_zero, Fin.cases_succ, hz, mul_zero, zero_add]
  have HS : (∑ j : Fin n, φ (a j.succ i) * mu j.succ) =
      (∑ j : Fin n, if j = h then φ (a j.succ i) * mu j.succ else 0) +
        ∑ j : Fin n, φ (a j.succ i) * (if j = h then 0 else mu j.succ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = h <;> simp [hj]
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] using HS.symm

theorem roots (φ : R →+* K) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R)
    (h : Fin n) (x : ι → K) (y : Fin n → K) (mu : Fin (n + 1) → K)
    (hz : mu 0 = 0)
    (hroot : ∀ j, j ≠ Sum.inr h.succ →
      (row p s a b j).eval₂ φ (Sum.elim x (Sum.elim y mu)) = 0) :
    ∀ j, (row p (s.erase h) (table a h) b j).eval₂ φ
      (Sum.elim x (Sum.elim y (multipliers mu h))) = 0 := by
  apply (roots_iff φ p (s.erase h) (table a h) b _).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [row, Fin.cases_zero, eval₂_rename, Function.comp_def,
      ambient, Sum.elim_inr, Sum.elim_inl] using hroot (Sum.inr 0)
        (by simpa only [ne_eq, Sum.inr.injEq] using (Fin.succ_ne_zero h).symm)
  · intro j hj
    obtain ⟨hjh, hjs⟩ := Finset.mem_erase.mp hj
    simpa only [row, Fin.cases_succ, ite_eq_left hjs, eval₂_sub,
      AffineHeightPolynomial.eval, eval₂_rename, sub_eq_zero, table,
      Fin.cases_succ, Function.comp_def, ambient, Sum.elim_inr, Sum.elim_inl] using
      hroot (Sum.inr j.succ) (by simpa only [ne_eq, Sum.inr.injEq, Fin.succ_inj] using hjh)
  · intro i
    have HG := hroot (Sum.inl i) (by simp)
    simp only [row, eval_gradient, sub_eq_zero, Function.comp_def, ambient, multiplier,
      Sum.elim_inr, Sum.elim_inl] at HG ⊢
    exact HG.trans (gradient_sum φ a mu h hz i).symm
  · intro j hj
    change multipliers mu h j.succ = 0
    by_cases he : j = h
    · simp only [multipliers, Fin.cases_succ, he, ite_true]
    · have hjs : j ∉ s := fun hs => hj (Finset.mem_erase.mpr ⟨he, hs⟩)
      have HU := hroot (Sum.inr j.succ) (by simpa only [ne_eq, Sum.inr.injEq, Fin.succ_inj] using he)
      simpa only [row, Fin.cases_succ, ite_eq_right hjs, eval₂_X, multiplier,
        Sum.elim_inr, multipliers, ite_eq_right he] using HU

end LeanCanny.Algebra.FlatAffineCriticalCoarsening
