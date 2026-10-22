/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayExtraneousLast
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Universal homogeneous systems with explicit coefficient groups

Each coefficient variable records its input coordinate and spatial
exponent. Permuting inputs and spatial coordinates together preserves the
coordinate-power specialization. Fixed-width sums give homogeneous universal
inputs and reconstruct every homogeneous system whose exponents fit.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped BigOperators Classical
variable {n : ℕ} {R : Type*} [CommRing R]

abbrev CoefficientIndex (n : ℕ) := Fin n × (Fin n →₀ ℕ)
abbrev CoefficientRing (n : ℕ) (R : Type*) [CommRing R] := MvPolynomial (CoefficientIndex n) R

noncomputable def system (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    MvPolynomial (Fin n) (CoefficientRing n R) :=
  ∑ r : Macaulay.Index n W,
    if (FixedWidthPolynomial.vector n W r).degree = d (π i) then
      MvPolynomial.monomial (FixedWidthPolynomial.vector n W r)
        (MvPolynomial.X (π i, Finsupp.equivMapDomain π (FixedWidthPolynomial.vector n W r)))
    else 0

theorem system_homogeneous (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (system (R := R) d W π i).IsHomogeneous (d (π i)) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro r _
  split_ifs with h
  · exact MvPolynomial.isHomogeneous_monomial _ h
  · exact MvPolynomial.isHomogeneous_zero _ _ _

theorem map_system_eq (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n))
    (point : CoefficientIndex n → R) (q : Fin n → MvPolynomial (Fin n) R)
    (hq : ∀ i, (q i).IsHomogeneous (d (π i)))
    (hbound : ∀ i m, m ∈ (q i).support → ∀ j, m j < 2 ^ W)
    (hpoint : ∀ i m, m.degree = d (π i) → point (π i, Finsupp.equivMapDomain π m) = (q i).coeff m)
    (i : Fin n) : (system (R := R) d W π i).map (MvPolynomial.eval point) = q i := by
  rw [system, map_sum]
  calc
    _ = ∑ r : Macaulay.Index n W,
        MvPolynomial.monomial (FixedWidthPolynomial.vector n W r) ((q i).coeff (FixedWidthPolynomial.vector n W r)) := by
      apply Finset.sum_congr rfl
      intro r _
      split_ifs with h
      · rw [MvPolynomial.map_monomial, MvPolynomial.eval_X, hpoint i _ h]
      · rw [map_zero, (hq i).coeff_eq_zero h, MvPolynomial.monomial_zero]
    _ = _ := FixedWidthPolynomial.sum_monomials_eq n W (q i) (hbound i)

theorem specialize_system (d : Fin n → ℕ) (W : ℕ) (p : Fin n → MvPolynomial (Fin n) R)
    (hp : ∀ i, (p i).IsHomogeneous (d i))
    (hbound : ∀ i m, m ∈ (p i).support → ∀ j, m j < 2 ^ W) (i : Fin n) :
    (system (R := R) d W (Equiv.refl _) i).map (MvPolynomial.eval (fun v => (p v.1).coeff v.2)) = p i := by
  apply map_system_eq d W (Equiv.refl _) _ p hp hbound
  intro j m _
  rw [Finsupp.equivMapDomain_refl]
  rfl

noncomputable def powerPoint (d : Fin n → ℕ) (v : CoefficientIndex n) : R :=
  if v.2 = Finsupp.single v.1 (d v.1) then 1 else 0

theorem permutedExponent_eq_single (π : Equiv.Perm (Fin n)) (m : Fin n →₀ ℕ) (i : Fin n) (D : ℕ) :
    Finsupp.equivMapDomain π m = Finsupp.single (π i) D ↔ m = Finsupp.single i D := by
  rw [← Finsupp.equivMapDomain_single π i D]
  exact (Finsupp.equivCongrLeft π).injective.eq_iff

theorem system_power_specialization (d : Fin n → ℕ) (W : ℕ) (hW : ∀ i, d i < 2 ^ W)
    (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (system (R := R) d W π i).map (MvPolynomial.eval (powerPoint (R := R) d)) =
      Macaulay.powers (R := R) (d ∘ π) i := by
  apply map_system_eq d W π _ (Macaulay.powers (R := R) (d ∘ π))
  · intro j
    exact MvPolynomial.isHomogeneous_monomial 1 (Finsupp.degree_single _ _)
  · intro j m hm k
    have he : m = Finsupp.single j (d (π j)) := by
      have hcoeff := MvPolynomial.mem_support_iff.mp hm
      change (MvPolynomial.monomial (Finsupp.single j (d (π j))) (1 : R)).coeff m ≠ 0 at hcoeff
      by_contra hne
      rw [MvPolynomial.coeff_monomial, ite_eq_right (Ne.symm hne)] at hcoeff
      exact hcoeff rfl
    rw [he]
    by_cases hk : k = j
    · simpa only [hk, Finsupp.single_eq_same] using hW (π j)
    · simpa only [Finsupp.single_eq_of_ne hk] using (Nat.two_pow_pos W)
  · intro j m _
    change (if Finsupp.equivMapDomain π m = Finsupp.single (π j) (d (π j)) then (1 : R) else 0) =
      (MvPolynomial.monomial (Finsupp.single j (d (π j))) (1 : R)).coeff m
    rw [MvPolynomial.coeff_monomial]
    have he := permutedExponent_eq_single π m j (d (π j))
    by_cases hm : m = Finsupp.single j (d (π j))
    · rw [ite_eq_left (he.mpr hm), ite_eq_left hm.symm]
    · rw [ite_eq_right (fun h => hm (he.mp h)), ite_eq_right (Ne.symm hm)]

end LeanCanny.Algebra.MacaulayUniversal
