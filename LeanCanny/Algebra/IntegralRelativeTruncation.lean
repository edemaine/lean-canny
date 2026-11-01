/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralRelativeLeadingNormalization

/-! # Branch-exact truncation before integer-leading normalization

A relative polynomial can lose degree on a selected algebra branch.
Discarding coefficients above that branch's actual degree preserves the
entire specialized polynomial. Subsequent inverse normalization retains
its exact roots and scalar degree without constructing an integer norm.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralRelativeTruncation
open Polynomial
open scoped Classical BigOperators
variable {A : Type*} [CommRing A]

noncomputable def truncate (p : Polynomial A) (d : ℕ) : Polynomial A :=
  ∑ k ∈ Finset.range (d + 1), monomial k (p.coeff k)

theorem coefficient (p : Polynomial A) (d k : ℕ) :
    (truncate p d).coeff k = if k ≤ d then p.coeff k else 0 := by
  simp [truncate, Polynomial.coeff_monomial, eq_comm]

theorem natDegree_le (p : Polynomial A) (d : ℕ) : (truncate p d).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coefficient, ite_eq_right (by omega)]

theorem map_eq (p : Polynomial A) (d : ℕ) (φ : A →ₐ[ℤ] ℝ) (hd : (p.map φ.toRingHom).natDegree ≤ d) :
    (truncate p d).map φ.toRingHom = p.map φ.toRingHom := by
  ext k
  rw [Polynomial.coeff_map, coefficient]
  by_cases hk : k ≤ d
  · rw [ite_eq_left hk, Polynomial.coeff_map]
  · rw [ite_eq_right hk, map_zero]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))).symm

theorem eval_eq (p : Polynomial A) (d : ℕ) (φ : A →ₐ[ℤ] ℝ) (hd : (p.map φ.toRingHom).natDegree ≤ d) (t : ℝ) :
    (truncate p d).eval₂ φ.toRingHom t = p.eval₂ φ.toRingHom t := by
  have H := congrArg (fun q : Polynomial ℝ => q.eval t) (map_eq p d φ hd)
  simpa only [Polynomial.eval_map] using H

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def normalized (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) :=
  IntegralRelativeLeadingNormalization.normalize b (truncate p d) d

theorem normalized_degree (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) (φ : A →ₐ[ℤ] ℝ) :
    ((normalized b p d).map φ.toRingHom).natDegree = d :=
  IntegralRelativeLeadingNormalization.specialized_degree b (truncate p d) d (natDegree_le p d) φ

theorem root_iff (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) (φ : A →ₐ[ℤ] ℝ)
    (hd : (p.map φ.toRingHom).natDegree = d) (hp : p.map φ.toRingHom ≠ 0) (t : ℝ) :
    (normalized b p d).eval₂ φ.toRingHom t = 0 ↔ p.eval₂ φ.toRingHom t = 0 := by
  have HA : φ ((truncate p d).coeff d) ≠ 0 := by
    rw [coefficient, ite_eq_left (Nat.le_refl d)]
    have H := Polynomial.leadingCoeff_ne_zero.mpr hp
    rw [Polynomial.leadingCoeff, hd, Polynomial.coeff_map] at H
    exact H
  exact (IntegralRelativeLeadingNormalization.root_iff b (truncate p d) d φ HA t).trans
    (congrArg (fun z : ℝ => z = 0) (eval_eq p d φ hd.le t)).to_iff

end LeanCanny.Algebra.IntegralRelativeTruncation
