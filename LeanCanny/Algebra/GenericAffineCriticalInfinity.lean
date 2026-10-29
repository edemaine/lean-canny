/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.GenericAffineCriticalJacobian
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! # Generic affine objectives on a homogeneous cone

A critical point of a homogeneous zero-level slice cannot be nonzero when
its objective coefficients are algebraically independent and its objective
multiplier is nonzero. Euler's identity forces the objective value to zero;
coordinate derivations then force every ambient coordinate to zero.
-/

@[expose] public section
namespace LeanCanny.Algebra.GenericAffineCriticalInfinity
open MvPolynomial GenericAffineCriticalJacobian
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {K L : Type*} {n : ℕ} [Field K] [Field L] [Algebra K L]

/-- Pairing a critical gradient with a vector tangent to the old heights
leaves only the new objective multiplier. -/
theorem gradient_pairing (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (v x y : Fin n → L) (μ : Fin (n + 1) → L)
    (hg : ∀ i, aeval x (pderiv i p) = v i * μ 0 + ∑ r, algebraMap K L (A r i) * μ r.succ)
    (hu : ∀ r, r ∉ s → μ r.succ = 0)
    (hy : ∀ r ∈ s, ∑ i, algebraMap K L (A r i) * y i = 0) :
    (∑ i, aeval x (pderiv i p) * y i) = μ 0 * ∑ i, v i * y i := by
  have hz : (∑ r, μ r.succ * ∑ i, algebraMap K L (A r i) * y i) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    by_cases hr : r ∈ s
    · rw [hy r hr, mul_zero]
    · rw [hu r hr, zero_mul]
  calc
    _ = μ 0 * (∑ i, v i * y i) +
        ∑ r, μ r.succ * ∑ i, algebraMap K L (A r i) * y i := by
      simp_rw [hg, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm (f := fun i r => algebraMap K L (A r i) * μ r.succ * y i)]
      congr 1 <;> apply Finset.sum_congr rfl
      · intro i _; ring
      · intro r _
        apply Finset.sum_congr rfl
        intro i _; ring
    _ = _ := by rw [hz, add_zero]

/-- The objective vanishes at a homogeneous-cone critical point with a
nonzero objective multiplier. -/
theorem objective_zero (p : MvPolynomial (Fin n) K) (D : ℕ) (hD : p.IsHomogeneous D)
    (s : Finset (Fin n)) (A : Fin n → Fin n → K) (v x : Fin n → L)
    (μ : Fin (n + 1) → L) (hp : aeval x p = 0)
    (hl : ∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = 0)
    (hg : ∀ i, aeval x (pderiv i p) = v i * μ 0 + ∑ r, algebraMap K L (A r i) * μ r.succ)
    (hu : ∀ r, r ∉ s → μ r.succ = 0) (hμ : μ 0 ≠ 0) : ∑ i, v i * x i = 0 := by
  have he := congrArg (aeval x) hD.sum_X_mul_pderiv
  simp only [map_sum, map_mul, aeval_X, map_nsmul, hp, nsmul_zero] at he
  have he' : (∑ i, aeval x (pderiv i p) * x i) = 0 := by
    simpa only [mul_comm] using he
  rw [gradient_pairing p s A v x x μ hg hu hl] at he'
  exact (mul_eq_zero.mp he').resolve_left hμ

/-- Generic objective coefficients have no nonzero cone critical point.
The field of coordinates may be any extension of the coefficient field. -/
theorem ambient_zero [CharZero K] (p : MvPolynomial (Fin n) K) (D : ℕ)
    (hD : p.IsHomogeneous D) (s : Finset (Fin n)) (A : Fin n → Fin n → K)
    (v x : Fin n → L) (μ : Fin (n + 1) → L) (hind : AlgebraicIndependent K v)
    (hp : aeval x p = 0) (hl : ∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = 0)
    (hg : ∀ i, aeval x (pderiv i p) = v i * μ 0 + ∑ r, algebraMap K L (A r i) * μ r.succ)
    (hu : ∀ r, r ∉ s → μ r.succ = 0) (hμ : μ 0 ≠ 0) : x = 0 := by
  have hvx := objective_zero p D hD s A v x μ hp hl hg hu hμ
  funext j
  obtain ⟨δ, hδ⟩ := CoordinateDerivation.exists_of_independent hind j
  have hsource : (∑ i, aeval x (pderiv i p) * δ (x i)) = 0 := by
    have H := congrArg δ hp
    simpa only [CriticalValueAlgebraic.chain_rule, map_zero] using H
  have hlevels (r : Fin n) (hr : r ∈ s) : ∑ i, algebraMap K L (A r i) * δ (x i) = 0 := by
    have H := congrArg δ (hl r hr)
    simpa only [map_sum, Derivation.leibniz, smul_eq_mul, Derivation.map_algebraMap,
      mul_zero, add_zero, map_zero] using H
  rw [gradient_pairing p s A v x (fun i => δ (x i)) μ hg hu hlevels] at hsource
  have htangent := (mul_eq_zero.mp hsource).resolve_left hμ
  have H := congrArg δ hvx
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, hδ, map_zero,
    Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, htangent, zero_add] at H
  exact H

/-- A positive-degree homogeneous polynomial vanishes at the origin. -/
theorem origin_zero (p : MvPolynomial (Fin n) K) (D : ℕ)
    (hD : p.IsHomogeneous D) (hD0 : 0 < D) : aeval (0 : Fin n → L) p = 0 := by
  have hz : (0 : Fin n →₀ ℕ).degree = 0 := map_zero Finsupp.degree
  have hc : p.coeff 0 = 0 := hD.coeff_eq_zero (by rw [hz]; omega)
  rw [aeval_zero, constantCoeff_eq, hc, map_zero]

/-- Positive-degree derivatives of a form of degree at least two vanish
at the origin, including the zero polynomial. -/
theorem gradient_origin_zero (p : MvPolynomial (Fin n) K) (D : ℕ)
    (hD : p.IsHomogeneous D) (hD2 : 1 < D) (i : Fin n) :
    aeval (0 : Fin n → L) (pderiv i p) = 0 := by
  exact origin_zero (pderiv i p) (D - 1) hD.pderiv (by omega)

/-- Transversality of the old cone slice supplies the nonzero multiplier. -/
theorem ambient_zero_of_independent [CharZero K] (p : MvPolynomial (Fin n) K) (D : ℕ)
    (hD : p.IsHomogeneous D) (s : Finset (Fin n)) (A : Fin n → Fin n → K)
    (v x : Fin n → L) (μ : Fin (n + 1) → L) (hind : AlgebraicIndependent K v)
    (hp : aeval x p = 0) (hl : ∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = 0)
    (hg : ∀ i, aeval x (pderiv i p) = v i * μ 0 + ∑ r, algebraMap K L (A r i) * μ r.succ)
    (hu : ∀ r, r ∉ s → μ r.succ = 0) (hconstraint : ConstraintIndependent p s A x) : x = 0 :=
  ambient_zero p D hD s A v x μ hind hp hl hg hu
    (multiplier_ne_zero p s A v x μ hg hu hconstraint)

end LeanCanny.Algebra.GenericAffineCriticalInfinity
