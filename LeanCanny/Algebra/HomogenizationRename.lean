/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogenizationAdditive

/-! # Ordinary homogenization commutes with variable renaming

The total exponent degree is preserved even when renamed variables merge.
The homogenizing variable is kept separate by `Option.map`.
-/

@[expose] public section
namespace LeanCanny.Algebra.WeightedHomogenization
open MvPolynomial
open scoped Classical
variable {σ τ R : Type*} [CommRing R]

private lemma optionElim_decompose (e : σ →₀ ℕ) (b : ℕ) :
    e.optionElim b = Finsupp.single none b + e.embDomain .some := by
  ext i
  cases i <;> simp

private lemma mapDomain_optionElim (f : σ → τ) (e : σ →₀ ℕ) (b : ℕ) :
    (e.optionElim b).mapDomain (Option.map f) = (e.mapDomain f).optionElim b := by
  rw [optionElim_decompose, optionElim_decompose, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  simp only [Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
  rfl

lemma exponent_mapDomain (f : σ → τ) (D : ℕ) (e : σ →₀ ℕ) :
    (exponent (fun _ => 1) D e).mapDomain (Option.map f) =
      exponent (fun _ => 1) D (e.mapDomain f) := by
  simp only [exponent, ← Finsupp.degree_eq_weight_one, Finsupp.degree_mapDomain]
  exact mapDomain_optionElim f e _

variable [Fintype σ] [Fintype τ]

theorem homogenize_rename (f : σ → τ) (D : ℕ) (p : MvPolynomial σ R) :
    homogenize (fun _ => 1) D (rename f p) =
      rename (Option.map f) (homogenize (fun _ => 1) D p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, homogenize_add, hp, hq]
  | monomial e a =>
    simp only [rename_monomial, homogenize_monomial, ← Finsupp.degree_eq_weight_one,
      Finsupp.degree_mapDomain]
    split_ifs
    · rw [rename_monomial, exponent_mapDomain]
    · rw [map_zero]

end LeanCanny.Algebra.WeightedHomogenization
