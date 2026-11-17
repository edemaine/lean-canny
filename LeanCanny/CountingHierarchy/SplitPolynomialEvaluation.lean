/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SumPolynomialSplitting

/-! # Evaluation after retaining a block as coefficient parameters -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial

variable {ι κ S : Type*} [CommRing S]

theorem eval_splitIntegerPolynomial (phi : ℤ →+* S) (x : ι → S) (z : κ → S)
    (p : MvPolynomial (ι ⊕ κ) ℤ) :
    MvPolynomial.eval₂ (MvPolynomial.eval₂Hom phi z) x (splitIntegerPolynomial p) =
      MvPolynomial.eval₂ phi (Sum.elim x z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [splitIntegerPolynomial_C, MvPolynomial.eval₂_C, MvPolynomial.coe_eval₂Hom]
  | add p q hp hq => simp only [map_add, MvPolynomial.eval₂_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul, hp]
    cases i <;> simp only [splitIntegerPolynomial_X_inl, splitIntegerPolynomial_X_inr,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, MvPolynomial.coe_eval₂Hom, Sum.elim_inl, Sum.elim_inr]

end LeanCanny.CountingHierarchy
