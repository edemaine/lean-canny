/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CoerciveComponentSampling
public import LeanCanny.Geometry.AlgebraicBranchLimit
public import LeanCanny.Algebra.ParametricCoerciveEliminant
/-! # An actual finite coercive-limit grid meets each isolated singular zero piece

The coordinate eliminants are constructed from the original polynomial.
Their lowest perturbation coefficients are nonzero. The bounded same-piece
critical limits satisfy them, supplying coverage without a smoothness or
annihilator premise on the original singular zero set.
-/
@[expose] public section
namespace LeanCanny.Geometry.CoerciveComponentEliminants
open Set Filter Polynomial MvPolynomial LeanCanny.Algebra
open scoped Topology Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem trailing_root (H : Polynomial (Polynomial ℝ)) (s t : ℕ → ℝ) (a : ℝ)
    (hs : ∀ k, s k≠0) (hs0 : Tendsto s atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 a))
    (hz : ∀ᶠ k in atTop, AlgebraicBranchLimit.value H (s k) (t k)=0) : H.trailingCoeff.eval a=0 := by
  obtain ⟨Q,HQ,H0⟩ := InfinitesimalSign.factor_at_trailingDegree H
  have HZ : ∀ᶠ k in atTop, AlgebraicBranchLimit.value Q (s k) (t k)=0 := by
    filter_upwards [hz] with k hk
    unfold AlgebraicBranchLimit.value at hk ⊢
    rw [HQ,Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_X] at hk
    exact (mul_eq_zero.mp hk).resolve_left (pow_ne_zero _ (hs k))
  have HL := (AlgebraicBranchLimit.continuous_value Q).continuousAt.tendsto.comp (hs0.prodMk_nhds ht)
  have HE : AlgebraicBranchLimit.value Q 0 a=0 := tendsto_nhds_unique HL
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr' (HZ.mono (fun _ h => h.symm)))
  simpa only [AlgebraicBranchLimit.value,Polynomial.eval₂_at_zero,H0,Polynomial.coe_evalRingHom] using HE

noncomputable def coordinate (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (i : Fin n) : Polynomial ℝ :=
  (ParametricCoerciveEliminant.polynomial q D i).trailingCoeff

theorem coordinate_ne_zero (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (hD : q.totalDegree≤D) (i : Fin n) :
    coordinate q D i≠0 :=
  Polynomial.trailingCoeff_ne_zero.mpr (ParametricCoerciveEliminant.ne_zero Complex.ofRealHom q D hD i)

noncomputable def grid (q : MvPolynomial (Fin n) ℝ) (D : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, (coordinate q D i).eval (x i)=0}

theorem finite_grid (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (hD : q.totalDegree≤D) : (grid q D).Finite :=
  Set.Finite.pi' (fun i => Polynomial.finite_setOfPred_isRoot (coordinate_ne_zero q D hD i))

theorem meets_piece (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (hD : q.totalDegree≤D)
    (hcompact : IsCompact (CoerciveComponentSampling.Zeros q))
    (C : Set (CoerciveComponentSampling.Zeros q)) (hC : IsClopen C)
    (x0 : CoerciveComponentSampling.Zeros q) (hx0 : x0∈C) :
    ∃ a : CoerciveComponentSampling.Zeros q, a∈C ∧ a.val∈grid q D := by
  let s : ℕ → ℝ := fun k => 1/((k : ℝ)+1)
  have HS : ∀ k, 0 < s k := fun k => by dsimp [s]; positivity
  have HS0 : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨y,a,φ,HA,Hφ,HL,_HB,HC⟩ := CoerciveComponentSampling.exists_critical_limits q D hcompact C hC x0 hx0 s HS HS0
  refine ⟨a,HA,?_⟩
  intro i
  apply trailing_root (ParametricCoerciveEliminant.polynomial q D i) (s ∘ φ) (fun k => y (φ k) i) (a.val i)
    (fun k => ne_of_gt (HS (φ k))) (HS0.comp Hφ.tendsto_atTop) ((continuous_apply i).continuousAt.tendsto.comp HL)
  filter_upwards [HC] with k hk
  have HX : ∀ j, eval (y (φ k)) (pderiv j (CoerciveCriticalFibers.polynomial (q.map (RingHom.id ℝ)) D (s (φ k))))=0 := by
    simpa only [MvPolynomial.map_id,CoercivePolynomialSampling.regularization,CoerciveCriticalFibers.polynomial] using hk
  exact ParametricCoerciveEliminant.eval_eq_zero (RingHom.id ℝ) q D hD i (s (φ k)) (y (φ k)) HX

end LeanCanny.Geometry.CoerciveComponentEliminants
