/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PartialDerivativeDegree
public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.Algebra.Polynomial.Roots

/-! # Finite critical fibers of coercive polynomial perturbations

A system with a nonzero pure coordinate power in each leading term admits
remainders with every coordinate exponent below that power. Its actual affine
coordinate quotient is a finite module. This applies to every gradient fiber
of q²+s∑Xᵢ^(2D+2), for s nonzero and D bounding the degree of q.
-/

@[expose] public section

namespace LeanCanny.Algebra.CoerciveCriticalFibers
open MvPolynomial
open scoped BigOperators Classical

variable {σ K : Type*} [Fintype σ] [Field K]

noncomputable def powerSystem (N : ℕ) (a : σ → K) (lower : σ → MvPolynomial σ K) (i : σ) :
    MvPolynomial σ K := monomial (Finsupp.single i N) (a i) + lower i

noncomputable def generated (p : σ → MvPolynomial σ K) : Ideal (MvPolynomial σ K) := Ideal.span (Set.range p)

omit [Fintype σ] in
private theorem leading_data [LinearOrder σ] [WellFoundedGT σ]
    (N : ℕ) (a : σ → K) (lower : σ → MvPolynomial σ K)
    (ha : ∀ i, a i ≠ 0) (hlower : ∀ i, (lower i).totalDegree < N) (i : σ) :
    MonomialOrder.degLex.degree (powerSystem N a lower i) = Finsupp.single i N ∧
      MonomialOrder.degLex.leadingCoeff (powerSystem N a lower i) = a i := by
  let m : MonomialOrder σ := MonomialOrder.degLex
  have hd : m.degree (monomial (Finsupp.single i N) (a i)) = Finsupp.single i N := by
    rw [MonomialOrder.degree_monomial, ite_eq_right (ha i)]
  have hlt : m.toSyn (m.degree (lower i)) < m.toSyn (Finsupp.single i N) := by
    change (toDegLex (MonomialOrder.degLex.degree (lower i)) : DegLex (σ →₀ ℕ)) <
      toDegLex (Finsupp.single i N)
    rw [Finsupp.DegLex.lt_iff]
    apply Or.inl
    simpa only [ofDegLex_toDegLex, MvPolynomial.degree_degLexDegree, Finsupp.degree_single] using hlower i
  have hlt' : m.toSyn (m.degree (lower i)) < m.toSyn (m.degree (monomial (Finsupp.single i N) (a i))) := by
    rw [hd]
    exact hlt
  constructor
  · exact (m.degree_add_of_lt hlt').trans hd
  · exact (m.leadingCoeff_add_of_lt hlt').trans (m.leadingCoeff_monomial (a i))

/-- Every class in the pure-leading-power quotient has a representative whose
individual variable degrees are at most N−1. -/
theorem exists_remainder (N : ℕ) (a : σ → K) (lower : σ → MvPolynomial σ K)
    (ha : ∀ i, a i ≠ 0) (hlower : ∀ i, (lower i).totalDegree < N) (f : MvPolynomial σ K) :
    ∃ r : MvPolynomial σ K, r ∈ restrictDegree σ K (N - 1) ∧
      Ideal.Quotient.mk (generated (powerSystem N a lower)) f =
        Ideal.Quotient.mk (generated (powerSystem N a lower)) r := by
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let m : MonomialOrder σ := MonomialOrder.degLex
  have hd (i : σ) := leading_data N a lower ha hlower i
  have hu (i : σ) : IsUnit (m.leadingCoeff (powerSystem N a lower i)) := by
    rw [hd i |>.2]
    exact isUnit_iff_ne_zero.mpr (ha i)
  obtain ⟨g, r, heq, _, hr⟩ := m.div hu f
  refine ⟨r, ?_, ?_⟩
  · apply (mem_restrictDegree σ r (N - 1)).mpr
    intro e he i
    have h := hr e he i
    rw [(hd i).1, Finsupp.single_le_iff] at h
    omega
  · have hm : Finsupp.linearCombination (MvPolynomial σ K) (powerSystem N a lower) g ∈
        generated (powerSystem N a lower) := by
      change (∑ i ∈ g.support, g i * powerSystem N a lower i) ∈ _
      apply Ideal.sum_mem
      intro i _
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    rw [heq, map_add, (Ideal.Quotient.eq_zero_iff_mem.mpr hm), zero_add]

/-- Division supplies a surjection from an explicit finite polynomial module
onto the actual generated quotient. -/
theorem quotient_finite (N : ℕ) (a : σ → K) (lower : σ → MvPolynomial σ K)
    (ha : ∀ i, a i ≠ 0) (hlower : ∀ i, (lower i).totalDegree < N) :
    Module.Finite K (MvPolynomial σ K ⧸ generated (powerSystem N a lower)) := by
  let I := generated (powerSystem N a lower)
  let π := (Ideal.Quotient.mkₐ K I).toLinearMap
  let φ : restrictDegree σ K (N - 1) →ₗ[K] MvPolynomial σ K ⧸ I :=
    π.comp (restrictDegree σ K (N - 1)).subtype
  apply Module.Finite.of_surjective φ
  intro z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨r, hr, he⟩ := exists_remainder N a lower ha hlower f
  exact ⟨⟨r, hr⟩, he.symm⟩

omit [Fintype σ] in
/-- A finite affine coordinate quotient supplies a genuine monic annihilator
for each coordinate, inside the original ideal rather than its radical. -/
theorem coordinate_annihilator (p : σ → MvPolynomial σ K)
    (hf : Module.Finite K (MvPolynomial σ K ⧸ generated p)) (i : σ) :
    ∃ q : Polynomial K, q.Monic ∧ Polynomial.aeval (X i : MvPolynomial σ K) q ∈ generated p := by
  let := hf
  obtain ⟨q, hq, he⟩ := IsIntegral.of_finite K (Ideal.Quotient.mk (generated p) (X i))
  refine ⟨q, hq, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  change (Ideal.Quotient.mkₐ K (generated p)) (Polynomial.aeval (X i : MvPolynomial σ K) q) = 0
  rw [← Polynomial.aeval_algHom_apply]
  exact he

theorem finite_zero_set (p : σ → MvPolynomial σ K)
    (hf : Module.Finite K (MvPolynomial σ K ⧸ generated p)) :
    {x : σ → K | ∀ i, MvPolynomial.eval x (p i) = 0}.Finite := by
  choose q hmonic hmem using coordinate_annihilator p hf
  apply (Set.Finite.pi' (fun i => Polynomial.finite_setOfPred_isRoot (hmonic i).ne_zero)).subset
  intro x hx i
  have hI : generated p ≤ RingHom.ker (MvPolynomial.eval x) := by
    apply Ideal.span_le.mpr
    rintro f ⟨j, rfl⟩
    exact hx j
  have he := hI (hmem i)
  change MvPolynomial.aeval x (Polynomial.aeval (X i : MvPolynomial σ K) (q i)) = 0 at he
  rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X] at he
  change Polynomial.eval (x i) (q i) = 0
  simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using he

/-- Adding a sufficiently high even diagonal power to a square. -/
noncomputable def polynomial (q : MvPolynomial σ K) (D : ℕ) (s : K) : MvPolynomial σ K :=
  q ^ 2 + C s * ∑ i : σ, X i ^ (2 * D + 2)

/-- The pure leading coefficient of every gradient equation. -/
def leadingScalar (D : ℕ) (s : K) : K := ((2 * D + 2 : ℕ) : K) * s

theorem gradient_eq (q : MvPolynomial σ K) (D : ℕ) (s : K) (i : σ) :
    pderiv i (polynomial q D s) =
      monomial (Finsupp.single i (2 * D + 1)) (leadingScalar D s) + pderiv i (q ^ 2) := by
  have hsum : pderiv i (∑ j : σ, (X j : MvPolynomial σ K) ^ (2 * D + 2)) =
      C ((2 * D + 2 : ℕ) : K) * X i ^ (2 * D + 1) := by
    rw [map_sum, Finset.sum_eq_single i]
    · rw [pderiv_pow, pderiv_X_self, mul_one]
      simp only [show 2 * D + 2 - 1 = 2 * D + 1 by omega, map_natCast]
    · intro j _ hji
      rw [pderiv_pow, pderiv_X_of_ne hji, mul_zero]
    · simp
  rw [polynomial, map_add, pderiv_C_mul, hsum]
  rw [← mul_assoc, ← map_mul, X_pow_eq_monomial, C_mul_monomial]
  simp only [leadingScalar, mul_comm s, mul_one]
  rw [add_comm]

omit [Fintype σ] in
theorem lower_degree (q : MvPolynomial σ K) (D : ℕ) (hD : q.totalDegree ≤ D) (i : σ) :
    (pderiv i (q ^ 2)).totalDegree < 2 * D + 1 := by
  have hp := MvPolynomial.totalDegree_pow q 2
  have hd := PartialDerivativeDegree.degree_le (q ^ 2) i
  have hm := Nat.mul_le_mul_left 2 hD
  omega

theorem leadingScalar_ne_zero [CharZero K] (D : ℕ) (s : K) (hs : s ≠ 0) : leadingScalar D s ≠ 0 :=
  mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hs

/-- Every fiber of the gradient has a finite actual affine coordinate algebra. -/
theorem gradient_quotient_finite [CharZero K] (q : MvPolynomial σ K) (D : ℕ)
    (hD : q.totalDegree ≤ D) (s : K) (hs : s ≠ 0) (v : σ → K) :
    Module.Finite K (MvPolynomial σ K ⧸ generated (fun i => pderiv i (polynomial q D s) - C (v i))) := by
  have hl (i : σ) : (pderiv i (q ^ 2) - C (v i)).totalDegree < 2 * D + 1 := by
    apply (MvPolynomial.totalDegree_sub _ _).trans_lt
    exact max_lt (lower_degree q D hD i) (by simp)
  have he : (fun i => pderiv i (polynomial q D s) - C (v i)) =
      powerSystem (2 * D + 1) (fun _ => leadingScalar D s) (fun i => pderiv i (q ^ 2) - C (v i)) := by
    funext i
    rw [gradient_eq]
    simp only [powerSystem, sub_eq_add_neg, add_assoc]
  rw [he]
  exact quotient_finite _ _ _ (fun _ => leadingScalar_ne_zero D s hs) hl

/-- Nonzero coercive perturbations have finite gradient fibers over every
characteristic-zero field, without any genericity or radical hypothesis. -/
theorem finite_gradient_fiber [CharZero K] (q : MvPolynomial σ K) (D : ℕ)
    (hD : q.totalDegree ≤ D) (s : K) (hs : s ≠ 0) (v : σ → K) :
    {x : σ → K | ∀ i, MvPolynomial.eval x (pderiv i (polynomial q D s)) = v i}.Finite := by
  have h := finite_zero_set (fun i => pderiv i (polynomial q D s) - C (v i))
    (gradient_quotient_finite q D hD s hs v)
  simpa only [MvPolynomial.eval_sub, MvPolynomial.eval_C, sub_eq_zero] using h

theorem finite_critical_points [CharZero K] (q : MvPolynomial σ K) (D : ℕ)
    (hD : q.totalDegree ≤ D) (s : K) (hs : s ≠ 0) :
    {x : σ → K | ∀ i, MvPolynomial.eval x (pderiv i (polynomial q D s)) = 0}.Finite :=
  finite_gradient_fiber q D hD s hs (fun _ => 0)

end LeanCanny.Algebra.CoerciveCriticalFibers
