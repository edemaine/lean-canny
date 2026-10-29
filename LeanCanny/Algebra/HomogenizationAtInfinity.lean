/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogeneousBadSystem
public import LeanCanny.Algebra.HomogenizationAdditive

/-! # Homogenization retains the leading form at infinity -/

@[expose] public section
namespace LeanCanny.Algebra.HomogenizationAtInfinity
open MvPolynomial WeightedHomogenization
open scoped Classical BigOperators
variable {σ R K : Type*} [Fintype σ] [CommRing R] [Field K]

omit [Fintype σ] in
theorem eval_homogeneous (φ : R →+* K) (p : MvPolynomial σ R) (D : ℕ)
    (hp : p.IsHomogeneous D) (y : Option σ → K) :
    (homogenize (fun _ => 1) D p).eval₂ φ y = p.eval₂ φ (y ∘ some) := by
  have hdeg (e : σ →₀ ℕ) (he : e ∈ p.support) : Finsupp.weight (fun _ => 1) e = D := by
    exact hp (mem_support_iff.mp he)
  have hf : p.support.filter (fun e => Finsupp.weight (fun _ => 1) e ≤ D) = p.support :=
    Finset.filter_eq_self.mpr (fun e he => (hdeg e he).le)
  rw [homogenize, hf, eval₂_sum]
  conv_rhs => rw [p.as_sum, eval₂_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval₂_monomial, eval₂_monomial, Finsupp.prod_option_index]
  · simp only [exponent, Finsupp.optionElim_apply_none, hdeg e he, Nat.sub_self, pow_zero,
      Finsupp.some_optionElim, one_mul, Function.comp_apply]
  · intro i; simp
  · intro i a b; exact pow_add _ _ _

theorem eval_lower (φ : R →+* K) (p : MvPolynomial σ R) (D : ℕ)
    (hp : p.totalDegree < D) (y : Option σ → K) (hy : y none = 0) :
    (homogenize (fun _ => 1) D p).eval₂ φ y = 0 := by
  rw [← eval_map, map_homogenize]
  exact CoerciveCriticalHomogenization.homogenize_eval_infinity (p.map φ) D
    ((PolynomialMapDegree.degree_le φ p).trans_lt hp) y hy

theorem eval_leading (φ : R →+* K) (low H : MvPolynomial σ R) (D : ℕ)
    (hlow : low.totalDegree < D) (hH : H.IsHomogeneous D) (y : Option σ → K) (hy : y none = 0) :
    (homogenize (fun _ => 1) D (H + low)).eval₂ φ y = H.eval₂ φ (y ∘ some) := by
  rw [homogenize_add, eval₂_add, eval_homogeneous φ H D hH y, eval_lower φ low D hlow y hy, add_zero]

end LeanCanny.Algebra.HomogenizationAtInfinity
