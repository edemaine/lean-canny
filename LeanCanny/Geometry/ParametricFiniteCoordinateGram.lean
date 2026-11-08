/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ParametricCoerciveBoxGramEliminant
public import LeanCanny.Algebra.IntegralParameterInverseSpecialization
public import LeanCanny.Geometry.CoerciveConstrainedSampling
public import LeanCanny.Geometry.CoerciveComponentEliminants
/-! # A fixed deformation slice captures finite parameterized coordinate images

The source and fixed Gram determinant are retained before specializing the
coefficient parameter. A nonzero original coefficient guards the lowest
deformation slice. Constrained coercive critical samples then capture every
point in a specialized finite coordinate image, including singular fibers.
-/
@[expose] public section
namespace LeanCanny.Geometry.ParametricFiniteCoordinateGram
open LeanCanny.Algebra MvPolynomial Filter Set
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

noncomputable def head (q : MvPolynomial (Fin n) (Polynomial ℤ)) (D : ℕ) (i : Fin n) :
    Polynomial (Polynomial ℤ) := (ParametricCoerciveBoxGramEliminant.polynomial q D i).trailingCoeff

noncomputable def exceptional (q : MvPolynomial (Fin n) (Polynomial ℤ)) (D : ℕ) (i : Fin n) :
    Polynomial ℤ := (head q D i).leadingCoeff

theorem head_ne_zero (q : MvPolynomial (Fin n) (Polynomial ℤ)) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) : head q D i ≠ 0 :=
  Polynomial.trailingCoeff_ne_zero.mpr (ParametricCoerciveBoxGramEliminant.ne_zero q D hD i)

theorem exceptional_ne_zero (q : MvPolynomial (Fin n) (Polynomial ℤ)) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) : exceptional q D i ≠ 0 :=
  Polynomial.leadingCoeff_ne_zero.mpr (head_ne_zero q D hD i)

private theorem trailing_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (H : Polynomial (Polynomial R)) (hH : H.trailingCoeff.map φ ≠ 0) :
    (H.map (Polynomial.mapRingHom φ)).trailingCoeff = H.trailingCoeff.map φ := by
  have HT := IntegralParameterInverse.natTrailingDegree_map_at (Polynomial.mapRingHom φ)
    H H.natTrailingDegree (fun k hk => by
      rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hk,map_zero]) hH
  simp only [Polynomial.trailingCoeff,HT,Polynomial.coeff_map,Polynomial.coe_mapRingHom]

private theorem mapped_value {R : Type*} [CommRing R] (φ : R →+* ℝ)
    (H : Polynomial (Polynomial R)) (s t : ℝ) :
    AlgebraicBranchLimit.value (ParametricCoerciveBoxGramEliminant.coefficientMap φ H) s t =
      ParametricCoerciveEliminant.specialize φ s t H := by
  have HC : (Polynomial.evalRingHom t).comp (Polynomial.mapRingHom φ) =
      Polynomial.eval₂RingHom φ t := by ext <;> simp
  unfold AlgebraicBranchLimit.value ParametricCoerciveBoxGramEliminant.coefficientMap
  change Polynomial.eval₂ (Polynomial.evalRingHom t) s (H.map (Polynomial.mapRingHom φ)) = _
  rw [Polynomial.eval₂_map,HC]
  rfl

theorem head_map_ne_zero (q : MvPolynomial (Fin n) (Polynomial ℤ)) (D : ℕ) (i : Fin n)
    (φ : Polynomial ℤ →+* ℝ) (hφ : φ (exceptional q D i) ≠ 0) : (head q D i).map φ ≠ 0 := by
  change φ (head q D i).leadingCoeff ≠ 0 at hφ
  apply Polynomial.leadingCoeff_ne_zero.mp
  simpa only [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ hφ] using hφ

theorem mapped_trailing (q : MvPolynomial (Fin n) (Polynomial ℤ)) (D : ℕ) (i : Fin n)
    (φ : Polynomial ℤ →+* ℝ) (hφ : φ (exceptional q D i) ≠ 0) :
    (ParametricCoerciveBoxGramEliminant.coefficientMap φ
      (ParametricCoerciveBoxGramEliminant.polynomial q D i)).trailingCoeff = (head q D i).map φ :=
  trailing_map φ _ (head_map_ne_zero q D i φ hφ)

theorem eval_head (q : MvPolynomial (Fin n) (Polynomial ℤ)) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) (φ : Polynomial ℤ →+* ℝ)
    (hφ : φ (exceptional q D i) ≠ 0)
    (hfinite : {t : ℝ | ∃ x : Fin n → ℝ, (q.map φ).eval x = 0 ∧ x i = t}.Finite)
    (x0 : Fin n → ℝ) (hroot : (q.map φ).eval x0 = 0) :
    (head q D i).eval₂ φ (x0 i) = 0 := by
  obtain ⟨y,a,sigma,hSigma,hlim,hai,_ha,hcritical⟩ :=
    CoerciveConstrainedSampling.exists_critical_samples_at_coordinate (q.map φ) D i x0 hroot hfinite
  have HT : Tendsto (fun k => y (sigma k) i) atTop (𝓝 (x0 i)) := by
    rw [←hai]
    exact (continuous_apply i).continuousAt.tendsto.comp hlim
  have H := CoerciveComponentEliminants.trailing_root
    (ParametricCoerciveBoxGramEliminant.coefficientMap φ
      (ParametricCoerciveBoxGramEliminant.polynomial q D i))
    (fun k => 1 / ((sigma k : ℝ)+1)) (fun k => y (sigma k) i) (x0 i)
    (fun k => by positivity)
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hSigma.tendsto_atTop) HT (by
      filter_upwards [hcritical] with k hk
      rw [mapped_value]
      exact ParametricCoerciveBoxGramEliminant.eval_eq_zero φ q D hD i _ (y (sigma k)) hk)
  rw [mapped_trailing q D i φ hφ,Polynomial.eval_map] at H
  exact H

end LeanCanny.Geometry.ParametricFiniteCoordinateGram
