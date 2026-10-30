/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PositivePolynomialSystem

/-! # Positive completion preserves a shift of an ordinary equation -/

@[expose] public section
namespace LeanCanny.Algebra.PositivePolynomialSystem
open MvPolynomial
open scoped Classical
variable {n : ℕ} {R K : Type*} [CommRing R] [CommRing K]

theorem extend_shifted (φ : R →+* K) (p : Fin n → MvPolynomial (Fin n) R)
    (z : Fin n → K) (r : Fin n) (v : K)
    (hz : ∀ i, (p i).eval₂ φ z = if i = r then v else 0) :
    ∀ i, (system p i).eval₂ φ (extend z) = if i = r.castSucc then v else 0 := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [new_row, eval₂_X, extend_last]
    have HN : Fin.last n ≠ r.castSucc := by
      intro he
      have HV := congrArg Fin.val he
      change n = r.val at HV
      have := r.isLt
      omega
    rw [ite_eq_right HN]
  · rw [old_row, eval₂_rename]
    have HE : extend z ∘ Fin.castSucc = z := funext (extend_old z)
    rw [HE, hz]
    simp only [Fin.castSucc_inj]

end LeanCanny.Algebra.PositivePolynomialSystem
