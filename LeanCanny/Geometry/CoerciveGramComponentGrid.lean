/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.PolynomialComponentPaths
public import LeanCanny.Geometry.PolynomialLimitAnnihilator
public import LeanCanny.Algebra.CoerciveBoxGramEliminant
/-! # Explicit integer Gram grids hit every original zero-set component

These fixed determinant heads can feed a diagonal finite sampler. The
original equation remains a filter on its own decoded point. No quotient
selection or regularity assumption on the original zero set is used.
-/
@[expose] public section
namespace LeanCanny.Geometry.CoerciveGramComponentGrid
open LeanCanny.Algebra Set Filter MvPolynomial
open CoerciveComponentSampling
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

noncomputable def head (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (i : Fin n) : Polynomial ℤ :=
  (CoerciveBoxGramEliminant.polynomial q D i).trailingCoeff

theorem head_ne_zero (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D) (i : Fin n) :
    head q D i ≠ 0 :=
  Polynomial.trailingCoeff_ne_zero.mpr (CoerciveBoxGramEliminant.ne_zero q D hD i)

def grid (q : MvPolynomial (Fin n) ℤ) (D : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, (head q D i).eval₂ (Int.castRingHom ℝ) (x i) = 0}

theorem finite_grid (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D) : (grid q D).Finite := by
  have hn (i : Fin n) : (head q D i).map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff Int.cast_injective).mpr (head_ne_zero q D hD i)
  simpa only [grid, Set.mem_ofPred_eq, Polynomial.IsRoot, Polynomial.eval_map] using
    Set.Finite.pi' (fun i => Polynomial.finite_setOfPred_isRoot (hn i))

/-- Critical limits remain in the requested clopen piece while the actual
integer Gram determinants pass to their nonzero trailing coefficients. -/
theorem meets_piece (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (C : Set (Zeros (q.map (Int.castRingHom ℝ)))) (hC : IsClopen C)
    (x : Zeros (q.map (Int.castRingHom ℝ))) (hx : x ∈ C) :
    ∃ a : Zeros (q.map (Int.castRingHom ℝ)), a ∈ C ∧ a.val ∈ grid q D := by
  let s : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hs : ∀ k, 0 < s k := by intro k; dsimp only [s]; positivity
  have hs0 : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨y, a, φ, ha, hφ, hlim, _, hcritical⟩ :=
    UnboundedCoerciveComponents.exists_critical_limits (q.map (Int.castRingHom ℝ)) D C hC x hx s hs hs0
  refine ⟨a, ha, fun i => ?_⟩
  apply PolynomialLimitAnnihilator.trailingCoeff_eval_eq_zero_of_eventually
    (CoerciveBoxGramEliminant.polynomial q D i) (s ∘ φ) (fun k => y (φ k) i) (a.val i)
    (fun k => ne_of_gt (hs (φ k))) (hs0.comp hφ.tendsto_atTop)
    ((continuous_apply i).continuousAt.tendsto.comp hlim)
  filter_upwards [hcritical] with k hk
  exact CoerciveBoxGramEliminant.eval_eq_zero q D hD i (s (φ k)) (y (φ k)) hk

theorem component_sample (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (x : Zeros (q.map (Int.castRingHom ℝ))) :
    ∃ a : Zeros (q.map (Int.castRingHom ℝ)), a ∈ connectedComponent x ∧ a.val ∈ grid q D := by
  let _ : Finite (ConnectedComponents (Zeros (q.map (Int.castRingHom ℝ)))) :=
    PolynomialFiniteComponents.components_finite _ D ((PolynomialMapDegree.degree_le _ _).trans hD)
  exact meets_piece q D hD (connectedComponent x) (FiniteComponentCover.isClopen_component x) x mem_connectedComponent

theorem joined_sample (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (x : Zeros (q.map (Int.castRingHom ℝ))) :
    ∃ a : Zeros (q.map (Int.castRingHom ℝ)),
      JoinedIn (Zeros (q.map (Int.castRingHom ℝ))) x.val a.val ∧ a.val ∈ grid q D := by
  obtain ⟨a, ha, hg⟩ := component_sample q D hD x
  exact ⟨a, PolynomialComponentPaths.subtype_joined _ x a ha, hg⟩

end LeanCanny.Geometry.CoerciveGramComponentGrid
