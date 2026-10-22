/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Variables

/-! # Common divisors of normalized polynomials omitting coefficient groups

Suppose every variable belongs to an input group, and the denominator for
each group omits that group's variables. A common divisor of all nonzero
denominators is constant. If the denominators specialize to one at a fixed
coefficient assignment, that common divisor is a unit over any domain.
-/

@[expose] public section

namespace LeanCanny.Algebra.GroupedPolynomialDivisors
open scoped Classical
variable {R σ ι : Type*} [CommRing R] [IsDomain R]

theorem vars_subset_of_dvd {p q : MvPolynomial σ R} (h : p ∣ q) (hq : q ≠ 0) : p.vars ⊆ q.vars := by
  obtain ⟨r, rfl⟩ := h
  have hp : p ≠ 0 := left_ne_zero_of_mul hq
  have hr : r ≠ 0 := right_ne_zero_of_mul hq
  intro i hi
  rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero] at hi ⊢
  rw [MvPolynomial.degreeOf_mul_eq hp hr]
  omega

theorem common_divisor_eq_constant (owner : σ → ι) (f : ι → MvPolynomial σ R)
    (hf : ∀ i, f i ≠ 0) (homit : ∀ i v, v ∈ (f i).vars → owner v ≠ i)
    (g : MvPolynomial σ R) (hg : ∀ i, g ∣ f i) : g = MvPolynomial.C (g.coeff 0) := by
  apply MvPolynomial.vars_eq_empty_iff_eq_C.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hmem := vars_subset_of_dvd (hg (owner v)) (hf (owner v)) hv
  exact homit (owner v) v hmem rfl

theorem isUnit_common_divisor [Nonempty ι] (owner : σ → ι) (f : ι → MvPolynomial σ R)
    (homit : ∀ i v, v ∈ (f i).vars → owner v ≠ i) (point : σ → R)
    (hnorm : ∀ i, MvPolynomial.eval point (f i) = 1)
    (g : MvPolynomial σ R) (hg : ∀ i, g ∣ f i) : IsUnit g := by
  have hf (i : ι) : f i ≠ 0 := by
    intro hz
    have h := hnorm i
    rw [hz, map_zero] at h
    exact zero_ne_one h
  have hc := common_divisor_eq_constant owner f hf homit g hg
  have hu : IsUnit (g.coeff 0) := by
    apply isUnit_of_dvd_one
    obtain ⟨q, hq⟩ := hg (Classical.arbitrary ι)
    refine ⟨MvPolynomial.eval point q, ?_⟩
    have h := congrArg (MvPolynomial.eval point) hq
    rw [hnorm, map_mul, hc, MvPolynomial.eval_C] at h
    exact h
  rw [hc]
  exact hu.map MvPolynomial.C

end LeanCanny.Algebra.GroupedPolynomialDivisors
