/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitution
public import LeanCanny.Algebra.CoefficientMass

/-! # Denominator-cleared composition of univariate rational coordinates

The clearing exponent is explicit and is unchanged by coefficient maps.
Composing a numerator and denominator uses the same exponent for both.
-/

@[expose] public section

namespace LeanCanny.Algebra.UnivariateRational
open Polynomial
open scoped BigOperators

noncomputable def clear {R : Type*} [CommSemiring R] (e : ℕ) (p n d : R[X]) : R[X] :=
  ∑ k ∈ Finset.range (e + 1), C (p.coeff k) * n ^ k * d ^ (e - k)

theorem eval₂_clear {R K : Type*} [CommSemiring R] [Field K] (phi : R →+* K)
    (e : ℕ) (p n d : R[X]) (hp : p.natDegree ≤ e) (x : K) (hd : d.eval₂ phi x ≠ 0) :
    (clear e p n d).eval₂ phi x = d.eval₂ phi x ^ e * p.eval₂ phi (n.eval₂ phi x / d.eval₂ phi x) := by
  simp only [clear, eval₂_finsetSum, eval₂_mul, eval₂_pow, eval₂_C]
  rw [eval₂_eq_sum_range' phi (by omega : p.natDegree < e + 1), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ e := by have := Finset.mem_range.mp hk; omega
  calc
    _ = phi (p.coeff k) * (d.eval₂ phi x ^ e * (n.eval₂ phi x / d.eval₂ phi x) ^ k) := by
      rw [RationalSubstitution.scale_div_pow _ _ _ _ hk' hd]
      ring
    _ = _ := by ring

theorem clear_degree {R : Type*} [CommSemiring R] (e : ℕ) (p n d : R[X]) (E : ℕ)
    (hn : n.natDegree ≤ E) (hd : d.natDegree ≤ E) : (clear e p n d).natDegree ≤ e * E := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hk' : k ≤ e := by have := Finset.mem_range.mp hk; omega
  calc
    _ ≤ (C (p.coeff k) * n ^ k).natDegree + (d ^ (e - k)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ k * E + (e - k) * E := Nat.add_le_add
      ((Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ hn)))
      (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ hd))
    _ = _ := by rw [← Nat.add_mul, Nat.add_sub_of_le hk']

theorem clear_map {R S : Type*} [CommSemiring R] [CommSemiring S] (phi : R →+* S)
    (e : ℕ) (p n d : R[X]) :
    (clear e p n d).map phi = clear e (p.map phi) (n.map phi) (d.map phi) := by
  simp only [clear, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.coeff_map]

theorem clear_mass (e : ℕ) (p n d : ℤ[X]) (hp : p.natDegree ≤ e) (M : ℕ)
    (hn : coefficientMass n ≤ M) (hd : coefficientMass d ≤ M) :
    coefficientMass (clear e p n d) ≤ coefficientMass p * M ^ e := by
  have hf (k : ℕ) (hk : k ∈ Finset.range (e + 1)) :
      coefficientMass (C (p.coeff k) * n ^ k * d ^ (e - k)) ≤ (p.coeff k).natAbs * M ^ e := by
    have hk' : k ≤ e := by have := Finset.mem_range.mp hk; omega
    calc
      _ ≤ (p.coeff k).natAbs * coefficientMass (n ^ k) * coefficientMass (d ^ (e - k)) := by
        apply (coefficientMass_mul_le _ _).trans
        rw [← coefficientMass_C (p.coeff k)]
        exact Nat.mul_le_mul_right _ (coefficientMass_mul_le _ _)
      _ ≤ (p.coeff k).natAbs * M ^ k * M ^ (e - k) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ ((coefficientMass_pow_le _ _).trans (Nat.pow_le_pow_left hn _)))
          ((coefficientMass_pow_le _ _).trans (Nat.pow_le_pow_left hd _))
      _ = _ := by rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hk']
  calc
    _ ≤ ∑ k ∈ Finset.range (e + 1), (p.coeff k).natAbs * M ^ e :=
      (coefficientMass_sum_le _ _).trans (Finset.sum_le_sum hf)
    _ = coefficientMass p * M ^ e := by
      rw [← Finset.sum_mul]
      congr 1
      exact (p.sum_over_range' (fun _ => rfl) (e + 1) (by omega)).symm

structure Coordinate where
  numerator : ℤ[X]
  denominator : ℤ[X]

namespace Coordinate

def degree (r : Coordinate) : ℕ := max r.numerator.natDegree r.denominator.natDegree

noncomputable def eval {K : Type*} [Field K] (r : Coordinate) (x : K) : K :=
  r.numerator.eval₂ (Int.castRingHom K) x / r.denominator.eval₂ (Int.castRingHom K) x

noncomputable def compWith (e : ℕ) (outer inner : Coordinate) : Coordinate :=
  ⟨clear e outer.numerator inner.numerator inner.denominator,
   clear e outer.denominator inner.numerator inner.denominator⟩

theorem compWith_degree (e : ℕ) (outer inner : Coordinate) : (compWith e outer inner).degree ≤ e * inner.degree :=
  max_le (clear_degree _ _ _ _ _ (le_max_left _ _) (le_max_right _ _))
    (clear_degree _ _ _ _ _ (le_max_left _ _) (le_max_right _ _))

theorem eval_compWith {K : Type*} [Field K] (e : ℕ) (outer inner : Coordinate) (he : outer.degree ≤ e) (x : K)
    (hd : inner.denominator.eval₂ (Int.castRingHom K) x ≠ 0) :
    (compWith e outer inner).eval x = outer.eval (inner.eval x) := by
  have hn : outer.numerator.natDegree ≤ e := (le_max_left _ _).trans he
  have hden : outer.denominator.natDegree ≤ e := (le_max_right _ _).trans he
  simp only [eval, compWith]
  rw [eval₂_clear (Int.castRingHom K) e outer.numerator inner.numerator inner.denominator hn x hd,
    eval₂_clear (Int.castRingHom K) e outer.denominator inner.numerator inner.denominator hden x hd]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hd)

theorem compWith_denominator_ne_zero {K : Type*} [Field K] (e : ℕ) (outer inner : Coordinate)
    (he : outer.degree ≤ e) (x : K) (hi : inner.denominator.eval₂ (Int.castRingHom K) x ≠ 0)
    (ho : outer.denominator.eval₂ (Int.castRingHom K) (inner.eval x) ≠ 0) :
    (compWith e outer inner).denominator.eval₂ (Int.castRingHom K) x ≠ 0 := by
  change (clear _ _ _ _).eval₂ _ _ ≠ 0
  rw [eval₂_clear (Int.castRingHom K) e outer.denominator inner.numerator inner.denominator
    ((le_max_right _ _).trans he) x hi]
  exact mul_ne_zero (pow_ne_zero _ hi) ho

theorem compWith_mass (e : ℕ) (outer inner : Coordinate) (he : outer.degree ≤ e) (s b : ℕ)
    (hon : coefficientMass outer.numerator ≤ 2 ^ s) (hod : coefficientMass outer.denominator ≤ 2 ^ s)
    (hin : coefficientMass inner.numerator ≤ 2 ^ b) (hid : coefficientMass inner.denominator ≤ 2 ^ b) :
    coefficientMass (compWith e outer inner).numerator ≤ 2 ^ (s + e * b) ∧
    coefficientMass (compWith e outer inner).denominator ≤ 2 ^ (s + e * b) := by
  have hpow : 2 ^ s * (2 ^ b) ^ e = 2 ^ (s + e * b) := by rw [← pow_mul, ← pow_add, Nat.mul_comm b]
  exact ⟨(clear_mass _ _ _ _ ((le_max_left _ _).trans he) _ hin hid).trans ((Nat.mul_le_mul_right _ hon).trans_eq hpow),
    (clear_mass _ _ _ _ ((le_max_right _ _).trans he) _ hin hid).trans ((Nat.mul_le_mul_right _ hod).trans_eq hpow)⟩

noncomputable def comp (outer inner : Coordinate) : Coordinate :=
  ⟨clear outer.degree outer.numerator inner.numerator inner.denominator,
   clear outer.degree outer.denominator inner.numerator inner.denominator⟩

theorem comp_degree (outer inner : Coordinate) : (comp outer inner).degree ≤ outer.degree * inner.degree :=
  compWith_degree outer.degree outer inner

theorem eval_comp {K : Type*} [Field K] (outer inner : Coordinate) (x : K)
    (hd : inner.denominator.eval₂ (Int.castRingHom K) x ≠ 0) :
    (comp outer inner).eval x = outer.eval (inner.eval x) :=
  eval_compWith outer.degree outer inner le_rfl x hd

theorem comp_denominator_ne_zero {K : Type*} [Field K] (outer inner : Coordinate) (x : K)
    (hi : inner.denominator.eval₂ (Int.castRingHom K) x ≠ 0)
    (ho : outer.denominator.eval₂ (Int.castRingHom K) (inner.eval x) ≠ 0) :
    (comp outer inner).denominator.eval₂ (Int.castRingHom K) x ≠ 0 :=
  compWith_denominator_ne_zero outer.degree outer inner le_rfl x hi ho

theorem comp_mass (outer inner : Coordinate) (s b : ℕ)
    (hon : coefficientMass outer.numerator ≤ 2 ^ s) (hod : coefficientMass outer.denominator ≤ 2 ^ s)
    (hin : coefficientMass inner.numerator ≤ 2 ^ b) (hid : coefficientMass inner.denominator ≤ 2 ^ b) :
    coefficientMass (comp outer inner).numerator ≤ 2 ^ (s + outer.degree * b) ∧
    coefficientMass (comp outer inner).denominator ≤ 2 ^ (s + outer.degree * b) :=
  compWith_mass outer.degree outer inner le_rfl s b hon hod hin hid

end Coordinate
end LeanCanny.Algebra.UnivariateRational
