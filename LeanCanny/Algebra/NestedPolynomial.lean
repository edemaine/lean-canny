/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Expanding polynomial coefficient parameters into a variable block

The standard sum-ring equivalence preserves evaluation and commutes with
renaming point variables and taking their formal partial derivatives.
-/

@[expose] public section

namespace LeanCanny.Algebra.NestedPolynomial
open MvPolynomial

variable {σ τ σ' R : Type*} [CommRing R]

noncomputable def flatten : MvPolynomial σ (MvPolynomial τ R) →+* MvPolynomial (Sum σ τ) R :=
  (sumRingEquiv R σ τ).symm.toRingHom

@[simp] theorem flatten_X (i : σ) : flatten (X i : MvPolynomial σ (MvPolynomial τ R)) = X (.inl i) :=
  sumRingEquiv_symm_X _ _ _ _

@[simp] theorem flatten_C_C (r : R) : flatten (C (C r) : MvPolynomial σ (MvPolynomial τ R)) = C r :=
  sumRingEquiv_symm_C_C _ _ _ _

@[simp] theorem flatten_C_X (i : τ) : flatten (C (X i) : MvPolynomial σ (MvPolynomial τ R)) = X (.inr i) :=
  sumRingEquiv_symm_C_X _ _ _ _

theorem flatten_C (p : MvPolynomial τ R) :
    flatten (C p : MvPolynomial σ (MvPolynomial τ R)) = rename Sum.inr p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, flatten_C_X, rename_X]

theorem flatten_rename (f : σ → σ') (p : MvPolynomial σ (MvPolynomial τ R)) :
    flatten (rename f p) = rename (Sum.map f id) (flatten p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [flatten_C, rename_rename, Function.comp_def]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp [hp]

theorem flatten_pderiv (p : MvPolynomial σ (MvPolynomial τ R)) (i : σ) :
    flatten (pderiv i p) = pderiv (.inl i) (flatten p) := by
  apply (sumRingEquiv R σ τ).injective
  have he (q : MvPolynomial σ (MvPolynomial τ R)) : sumRingEquiv R σ τ (flatten q) = q :=
    RingEquiv.apply_symm_apply _ _
  rw [he]
  have h := pderiv_sumRingEquiv (R := R) (σ := σ) (ι := τ) (flatten p) i
  rw [he] at h
  exact h

theorem flatten_map_C (p : MvPolynomial σ R) :
    flatten (p.map (C : R →+* MvPolynomial τ R)) = rename Sum.inl p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp [hp]

theorem eval_flatten {S : Type*} [CommRing S] (φ : R →+* S) (x : σ → S) (y : τ → S)
    (p : MvPolynomial σ (MvPolynomial τ R)) :
    (flatten p).eval₂ φ (Sum.elim x y) = p.eval₂ (eval₂Hom φ y) x := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [flatten_C, eval₂_rename, Function.comp_def]
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | mul_X p i hp => simp [hp]

end LeanCanny.Algebra.NestedPolynomial
