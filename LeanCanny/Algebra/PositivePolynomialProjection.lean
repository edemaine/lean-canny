/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PositivePolynomialSystem

/-! # Projections preserve the extra zero equation of a positive completion -/

@[expose] public section
namespace LeanCanny.Algebra.PositivePolynomialSystem
open MvPolynomial
variable {R : Type*} [CommRing R] {n m : ℕ}

lemma rename_projection (p : Fin n → MvPolynomial (Fin n) R) (q : Fin m → MvPolynomial (Fin m) R)
    (pi : Fin n → Fin m) (rho : Fin (n + 1) → Fin (m + 1))
    (hold : rho ∘ Fin.castSucc = Fin.castSucc ∘ pi)
    (hlast : rho (Fin.last n) = Fin.last m) (hsystem : ∀ i, rename pi (p i) = q (pi i))
    (i : Fin (n + 1)) : rename rho (system p i) = system q (rho i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [new_row, rename_X, hlast, new_row]
  · have HO : rho j.castSucc = (pi j).castSucc := congrFun hold j
    rw [old_row, HO, old_row, rename_rename, hold, ← rename_rename, hsystem]

end LeanCanny.Algebra.PositivePolynomialSystem
