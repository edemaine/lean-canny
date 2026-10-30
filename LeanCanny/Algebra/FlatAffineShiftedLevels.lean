/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCriticalStage

/-! # An affine height shift as one extra frozen ancestral coordinate -/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineShiftedLevels
open MvPolynomial FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {ι R K : Type*} {n : ℕ} [CommRing R] [CommRing K]

noncomputable def levels (b : Fin n → MvPolynomial ι R) (h : Fin n) (j : Fin n) :
    MvPolynomial (ι ⊕ Unit) R := rename Sum.inl (b j) + if j = h then X (Sum.inr ()) else 0

def point (x : ι → K) (v : K) : ι ⊕ Unit → K := Sum.elim x (fun _ => v)

theorem eval (φ : R →+* K) (b : Fin n → MvPolynomial ι R) (h j : Fin n)
    (x : ι → K) (v : K) :
    (levels b h j).eval₂ φ (point x v) = (b j).eval₂ φ x + if j = h then v else 0 := by
  rw [levels, eval₂_add, eval₂_rename]
  have HE : point x v ∘ Sum.inl = x := rfl
  rw [HE]
  by_cases hj : j = h <;> simp only [hj, ite_true, ite_false, eval₂_X, point, Sum.elim_inr, eval₂_zero]

theorem row_eval (φ : R →+* K) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R)
    (h : Fin n) (hs : h ∈ s) (x : ι → K) (y : Variables n → K) (v : K) (j : Variables n) :
    (row p s a (levels b h) j).eval₂ φ (Sum.elim (point x v) y) =
      (row p s a b j).eval₂ φ (Sum.elim x y) - if j = Sum.inr h.succ then v else 0 := by
  cases j with
  | inl i =>
    simp only [row, eval_gradient, Function.comp_def, ambient, multiplier, Sum.elim_inr,
      Sum.inl_ne_inr, ite_false, sub_zero]
  | inr r =>
    refine Fin.cases ?_ (fun j => ?_) r
    · simp only [row, Fin.cases_zero, eval₂_rename, Function.comp_def, ambient,
        Sum.elim_inr, Sum.inr.injEq, (Fin.succ_ne_zero h).symm, ite_false, sub_zero]
    · by_cases hjs : j ∈ s
      · simp only [row, Fin.cases_succ, ite_eq_left hjs, eval₂_sub, AffineHeightPolynomial.eval,
          eval₂_rename, Function.comp_def, ambient, Sum.elim_inr, Sum.elim_inl,
          Sum.inr.injEq, Fin.succ_inj]
        have HE := eval φ b h j x v
        change _ - (levels b h j).eval₂ φ (point x v) = _
        rw [HE]
        ring
      · have hjh : j ≠ h := fun he => hjs (he.symm ▸ hs)
        simp only [row, Fin.cases_succ, ite_eq_right hjs, eval₂_X, multiplier,
          Sum.elim_inr, Sum.inr.injEq, Fin.succ_inj, ite_eq_right hjh, sub_zero]

end LeanCanny.Algebra.FlatAffineShiftedLevels
