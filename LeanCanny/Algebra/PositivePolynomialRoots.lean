/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PositivePolynomialSystem

/-! # Removing the unique zero dummy gives an equivalence of root sets -/

@[expose] public section
namespace LeanCanny.Algebra.PositivePolynomialSystem
open MvPolynomial
variable {n : ℕ} {R K : Type*} [CommRing R] [CommRing K]

noncomputable def rootsEquiv (phi : R →+* K) (p : Fin n → MvPolynomial (Fin n) R) :
    {z : Fin (n + 1) → K // ∀ i, (system p i).eval₂ phi z = 0} ≃
    {z : Fin n → K // ∀ i, (p i).eval₂ phi z = 0} where
  toFun z := ⟨z.val ∘ Fin.castSucc, ((roots_iff phi p z.val).mp z.property).1⟩
  invFun z := ⟨extend z.val, (roots_extend_iff phi p z.val).mpr z.property⟩
  left_inv z := Subtype.ext (eq_extend z.val ((roots_iff phi p z.val).mp z.property).2)
  right_inv z := Subtype.ext (funext (extend_old z.val))

end LeanCanny.Algebra.PositivePolynomialSystem
