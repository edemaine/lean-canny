/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.TiltedCoerciveComponentSampling
public import LeanCanny.Geometry.CoerciveComponentEliminants
public import LeanCanny.Algebra.ParametricTiltedCoerciveEliminant
/-! # One finite tilted-limit grid meets every positive clopen piece

The coordinate eliminants have no threshold parameter. Positivity and the
chosen label are retained by the constructed tilted critical limits.
-/
@[expose] public section
namespace LeanCanny.Geometry.TiltedCoerciveComponentEliminants
open Set Filter Polynomial MvPolynomial LeanCanny.Algebra
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

noncomputable def coordinate (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (u i : Fin n) : Polynomial ℝ :=
  (ParametricTiltedCoerciveEliminant.polynomial q D u i).trailingCoeff

theorem coordinate_ne_zero (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (hD : q.totalDegree≤D) (u i : Fin n) :
    coordinate q D u i≠0 := Polynomial.trailingCoeff_ne_zero.mpr
  (ParametricTiltedCoerciveEliminant.ne_zero Complex.ofRealHom q D hD u i)

noncomputable def grid (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (u : Fin n) : Set (Fin n → ℝ) :=
  {x | ∀ i, (coordinate q D u i).eval (x i)=0}

theorem finite_grid (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (hD : q.totalDegree≤D) (u : Fin n) :
    (grid q D u).Finite :=
  Set.Finite.pi' (fun i => Polynomial.finite_setOfPred_isRoot (coordinate_ne_zero q D hD u i))

theorem meets_positive_piece (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (hD : q.totalDegree≤D) (u : Fin n)
    (hcompact : IsCompact (CoerciveComponentSampling.Zeros q))
    (C : Set (TiltedCoerciveComponentSampling.Positive q u)) (hC : IsClopen C)
    (x0 : TiltedCoerciveComponentSampling.Positive q u) (hx0 : x0∈C) :
    ∃ a : TiltedCoerciveComponentSampling.Positive q u, a∈C ∧
      x0.val.val u≤a.val.val u ∧ a.val.val∈grid q D u := by
  let s : ℕ → ℝ := fun k => 1/((k : ℝ)+1)
  have HS : ∀ k, 0 < s k := fun k => by dsimp [s]; positivity
  have HS0 : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨y,a,φ,HA,Hφ,HL,HU,HC⟩ := TiltedCoerciveComponentSampling.exists_positive_critical_limits
    q D u hcompact C hC x0 hx0 s HS HS0
  refine ⟨a,HA,HU,?_⟩
  intro i
  apply CoerciveComponentEliminants.trailing_root
    (ParametricTiltedCoerciveEliminant.polynomial q D u i) (s ∘ φ) (fun k => y (φ k) i) (a.val.val i)
    (fun k => ne_of_gt (HS (φ k))) (HS0.comp Hφ.tendsto_atTop) ((continuous_apply i).continuousAt.tendsto.comp HL)
  filter_upwards [HC] with k hk
  have HX : ∀ j, eval (y (φ k)) (pderiv j
      (TiltedCoerciveCriticalFibers.polynomial (q.map (RingHom.id ℝ)) D u (s (φ k))))=0 := by
    simpa only [MvPolynomial.map_id,TiltedCoerciveComponentSampling.polynomial,
      CoercivePolynomialSampling.regularization,TiltedCoerciveCriticalFibers.polynomial] using hk
  exact ParametricTiltedCoerciveEliminant.eval_eq_zero (RingHom.id ℝ) q D hD u i (s (φ k)) (y (φ k)) HX

end LeanCanny.Geometry.TiltedCoerciveComponentEliminants
