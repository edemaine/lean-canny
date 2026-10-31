/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Polynomial.IntegralNormalization
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # Monic parameter equations with a fixed advertised degree

Use the selected coefficient at degree d rather than the formal leading
coefficient. The equation stays monic of degree d even at branches where
that coefficient vanishes. After a specialization preserving the selected
degree it is exactly the usual integral normalization.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedDegreeIntegralNormalization
open Polynomial
open scoped BigOperators Classical

variable {R : Type*} [CommRing R]

noncomputable def polynomial (p : Polynomial R) (d : ℕ) : Polynomial R :=
  X ^ d + ∑ i ∈ Finset.range d, monomial i (p.coeff i * p.coeff d ^ (d - 1 - i))

theorem coefficient (p : Polynomial R) (d k : ℕ) :
    (polynomial p d).coeff k =
      (if k = d then 1 else 0) + (if k < d then p.coeff k * p.coeff d ^ (d - 1 - k) else 0) := by
  simp [polynomial, Polynomial.coeff_monomial, eq_comm]

theorem coefficient_top (p : Polynomial R) (d : ℕ) : (polynomial p d).coeff d = 1 := by
  simp only [coefficient, ↓reduceIte, Nat.lt_irrefl, add_zero]

theorem coefficient_above (p : Polynomial R) (d k : ℕ) (hk : d < k) : (polynomial p d).coeff k = 0 := by
  rw [coefficient, ite_eq_right (by omega), ite_eq_right (by omega), zero_add]

theorem natDegree_le (p : Polynomial R) (d : ℕ) : (polynomial p d).natDegree ≤ d :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun _ hk => coefficient_above p d _ hk)

theorem natDegree [Nontrivial R] (p : Polynomial R) (d : ℕ) : (polynomial p d).natDegree = d :=
  Nat.le_antisymm (natDegree_le p d)
    (Polynomial.le_natDegree_of_ne_zero (by rw [coefficient_top]; exact one_ne_zero))

theorem monic [Nontrivial R] (p : Polynomial R) (d : ℕ) : (polynomial p d).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, natDegree, coefficient_top]

theorem map {S : Type*} [CommRing S] (p : Polynomial R) (d : ℕ) (φ : R →+* S) :
    (polynomial p d).map φ = polynomial (p.map φ) d := by
  ext k
  simp only [Polynomial.coeff_map, coefficient, map_add]
  split_ifs <;> simp

theorem eq_integralNormalization [Nontrivial R] (p : Polynomial R) (d : ℕ)
    (hp : p ≠ 0) (hd : p.natDegree = d) : polynomial p d = p.integralNormalization := by
  ext k
  by_cases hk : k = d
  · subst k
    rw [coefficient_top, ← hd, integralNormalization_coeff_natDegree hp]
  · rw [coefficient, ite_eq_right hk, zero_add, integralNormalization_coeff_ne_natDegree (by omega)]
    by_cases hlt : k < d
    · rw [ite_eq_left hlt]
      simp only [Polynomial.leadingCoeff, hd]
    · rw [ite_eq_right hlt, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

theorem map_eq_integralNormalization {S : Type*} [CommRing S] [Nontrivial S]
    (p : Polynomial R) (d : ℕ) (φ : R →+* S) (hp : p.map φ ≠ 0) (hd : (p.map φ).natDegree = d) :
    (polynomial p d).map φ = (p.map φ).integralNormalization :=
  (map p d φ).trans (eq_integralNormalization (p.map φ) d hp hd)

theorem scaled_root {K : Type*} [Field K] (p : Polynomial R) (d : ℕ) (φ : R →+* K)
    (hd : (p.map φ).natDegree = d) (hpos : 1 ≤ d) (x : K) (hx : p.eval₂ φ x = 0) :
    (polynomial p d).eval₂ φ (φ (p.coeff d) * x) = 0 := by
  have hp : p.map φ ≠ 0 := by intro h; rw [h, Polynomial.natDegree_zero] at hd; omega
  have HE := integralNormalization_eval₂_leadingCoeff_mul (p := p.map φ) (by omega) (RingHom.id K) x
  have HC : (p.map φ).leadingCoeff = φ (p.coeff d) := by rw [Polynomial.leadingCoeff, hd, Polynomial.coeff_map]
  have HN := map_eq_integralNormalization p d φ hp hd
  have HV := congrArg (fun q : Polynomial K => q.eval (φ (p.coeff d) * x)) HN
  simp only [Polynomial.eval_map] at HV
  have Hroot : (p.map φ).eval x = 0 := by simpa only [Polynomial.eval_map] using hx
  rw [HV, ← HC]
  simpa only [RingHom.id_apply, Polynomial.eval₂_id, Hroot, mul_zero] using HE

end LeanCanny.Algebra.FixedDegreeIntegralNormalization
