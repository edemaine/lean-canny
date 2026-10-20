/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.IntegerProjectionDirections
public import LeanCanny.Geometry.PolynomialRationalAvoidance
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic.Linarith

/-! # Nearby rational directions with finite projection root sets

Avoid the finite family's exceptional polynomials inside a small rational
coordinate grid. Thus every neighborhood of a normalized real direction has
a normalized rational direction giving finite roots for the whole regular
hypersurface family. No uniform numerator or denominator bound is supplied.
-/

@[expose] public section

namespace LeanCanny.Geometry.ProjectionCritical
open Set MvPolynomial
open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def rationalDirection (base : ι)
    (u : Algebra.ProjectionFiniteSpecialization.DirectionIndex base → ℚ) : ι → ℝ :=
  Algebra.ProjectionFiniteSpecialization.normalizedDirection base (fun i => (u i : ℝ))

def IsRationalDirection (base : ι) (v : ι → ℝ) : Prop :=
  ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex base → ℚ, rationalDirection base u = v

omit [Fintype ι] in
theorem rationalDirection_base (base : ι) (u : Algebra.ProjectionFiniteSpecialization.DirectionIndex base → ℚ) :
    rationalDirection base u base = 1 := by
  classical
  simp [rationalDirection, Algebra.ProjectionFiniteSpecialization.normalizedDirection]

theorem exists_rational_direction_avoiding (base : ι) (v : ι → ℝ) (hv : v base = 1)
    (U : Set (ι → ℝ)) (hU : U ∈ nhds v)
    (d : Algebra.ProjectionFiniteSpecialization.ParameterRing ℝ base) (hd : d ≠ 0) :
    ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex base → ℚ,
      rationalDirection base u ∈ U ∧ MvPolynomial.eval (fun i => (u i : ℝ)) d ≠ 0 := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨u, hb, he⟩ := PolynomialRationalAvoidance.exists_in_intervals d hd
    (fun i => v i - r) (fun i => v i + r) (fun i => by linarith)
  have hdist : ∀ i, dist (rationalDirection base u i) (v i) < r := by
    intro i
    by_cases hi : i = base
    · subst i
      rw [rationalDirection_base, hv, dist_self]
      exact hr
    · have hbi := hb ⟨i, hi⟩
      simp only [rationalDirection, Algebra.ProjectionFiniteSpecialization.normalizedDirection,
        dite_eq_right hi, Real.dist_eq, abs_lt]
      constructor <;> linarith [hbi.1, hbi.2]
  exact ⟨u, hball ((dist_pi_lt_iff hr).mpr hdist), he⟩

theorem exists_common_rational_direction_near {σ : Type*} [Fintype σ]
    (p : σ → MvPolynomial ι ℝ) (base : ι)
    (hregular : ∀ j (x : ι → ℝ), (p j).eval₂ (RingHom.id ℝ) x = 0 →
      Function.Surjective (fderiv ℝ (fun y => (p j).eval₂ (RingHom.id ℝ) y) x))
    (v : ι → ℝ) (hv : v base = 1) (U : Set (ι → ℝ)) (hU : U ∈ nhds v) :
    ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex base → ℚ, rationalDirection base u ∈ U ∧
      ∀ j, {x : ι → ℝ | ∀ k, (Algebra.ProjectionEquations.system (p j) base k).eval₂ (RingHom.id ℝ)
        (Sum.elim x (rationalDirection base u)) = 0}.Finite := by
  classical
  choose d hd hfinite using fun j => Algebra.ProjectionFiniteSpecialization.exists_exceptional_polynomial (p j) base
  have hprod : (∏ j, d j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hd j)
  obtain ⟨u, hu, he⟩ := exists_rational_direction_avoiding base v hv U hU (∏ j, d j) hprod
  rw [map_prod] at he
  refine ⟨u, hu, ?_⟩
  intro j
  apply finite_roots_of_extended (p j) base (rationalDirection base u) (rationalDirection_base base u) ?_ (hregular j)
  apply hfinite j ℝ (fun i => (u i : ℝ))
  exact Finset.prod_ne_zero_iff.mp he j (Finset.mem_univ j)

theorem exists_common_rational_direction_near_of_coefficients {R σ : Type*} [CommRing R] [Fintype σ]
    (φ : R →+* ℝ) (p : σ → MvPolynomial ι R) (base : ι)
    (hregular : ∀ j (x : ι → ℝ), (p j).eval₂ φ x = 0 →
      Function.Surjective (fderiv ℝ (fun y => (p j).eval₂ φ y) x))
    (v : ι → ℝ) (hv : v base = 1) (U : Set (ι → ℝ)) (hU : U ∈ nhds v) :
    ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex base → ℚ, rationalDirection base u ∈ U ∧
      ∀ j, {x : ι → ℝ | ∀ k, (Algebra.ProjectionEquations.system (p j) base k).eval₂ φ
        (Sum.elim x (rationalDirection base u)) = 0}.Finite := by
  have heval (q : MvPolynomial ι R) (x : ι → ℝ) : (q.map φ).eval₂ (RingHom.id ℝ) x = q.eval₂ φ x := by
    rw [eval₂_map, RingHom.id_comp]
  have hreg : ∀ j (x : ι → ℝ), ((p j).map φ).eval₂ (RingHom.id ℝ) x = 0 →
      Function.Surjective (fderiv ℝ (fun y => ((p j).map φ).eval₂ (RingHom.id ℝ) y) x) := by
    intro j x hx
    rw [heval] at hx
    have hfun : (fun y : ι → ℝ => ((p j).map φ).eval₂ (RingHom.id ℝ) y) = fun y => (p j).eval₂ φ y :=
      funext (heval (p j))
    rw [hfun]
    exact hregular j x hx
  obtain ⟨u, hu, hfinite⟩ := exists_common_rational_direction_near (fun j => (p j).map φ) base hreg v hv U hU
  refine ⟨u, hu, ?_⟩
  intro j
  apply (hfinite j).subset
  intro x hx k
  rw [system_eval_map]
  exact hx k

end LeanCanny.Geometry.ProjectionCritical
