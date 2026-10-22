/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.LevelProjectionSpecialization
public import LeanCanny.Algebra.InfinitesimalSign
public import LeanCanny.Geometry.RationalProjectionDirections

/-! # Rational directions uniform over a small positive level interval

A nonzero joint exceptional polynomial has a nonzero coefficient when viewed
as a polynomial in the level. Choose a nearby rational direction avoiding
that coefficient. The specialized level polynomial stays nonzero throughout
some positive interval, so every extended projection fiber there is finite.
The same direction works for any finite family of hypersurfaces.
-/

@[expose] public section

namespace LeanCanny.Geometry.ProjectionCritical
open Set MvPolynomial
open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι]

theorem exists_rational_direction_avoiding_levels (base : ι) (v : ι → ℝ) (hv : v base = 1)
    (U : Set (ι → ℝ)) (hU : U ∈ nhds v)
    (d : Algebra.LevelProjectionSpecialization.ParameterRing ℝ base) (hd : d ≠ 0) :
    ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex base → ℚ,
      rationalDirection base u ∈ U ∧ ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
        MvPolynomial.eval (fun t => t.elim alpha (fun i => (u i : ℝ))) d ≠ 0 := by
  let q := optionEquivLeft ℝ (Algebra.ProjectionFiniteSpecialization.DirectionIndex base) d
  have hq : q ≠ 0 := (map_ne_zero_iff (optionEquivLeft ℝ _) (optionEquivLeft ℝ _).injective).mpr hd
  obtain ⟨u, hu, he⟩ := exists_rational_direction_avoiding base v hv U hU q.leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr hq)
  let r := q.map (MvPolynomial.eval (fun i => (u i : ℝ)))
  have hr : r ≠ 0 := by
    intro hzero
    have hc := congrArg (fun f : Polynomial ℝ => f.coeff q.natDegree) hzero
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coeff_natDegree] at hc
    exact he hc
  obtain ⟨a, ha, hs⟩ := Algebra.InfinitesimalSign.sign_eval_eq_trailingCoeff r
  refine ⟨u, hu, a, ha, ?_⟩
  intro alpha hp hl hz
  have hz' : r.eval alpha = 0 := by
    rw [← optionEquivLeft_elim_eval ℝ _ (fun i => (u i : ℝ)) alpha d]
    exact hz
  have hsign := hs alpha hp hl
  rw [hz', sign_zero] at hsign
  exact (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hr) (sign_eq_zero_iff.mp hsign.symm)

theorem exists_common_rational_extended_direction_near {σ : Type*} [Fintype σ]
    (p : σ → MvPolynomial ι ℝ) (base : ι)
    (v : ι → ℝ) (hv : v base = 1) (U : Set (ι → ℝ)) (hU : U ∈ nhds v) :
    ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex base → ℚ,
      rationalDirection base u ∈ U ∧ ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
        ∀ j, {z : Option ι → ℝ | ∀ k, aeval z (Algebra.GenericProjectionFinite.equation
          (Algebra.LevelProjectionSpecialization.levelPolynomial (p j) alpha) base (rationalDirection base u) k) = 0}.Finite := by
  classical
  choose d hd hfinite using fun j => Algebra.LevelProjectionSpecialization.exists_exceptional_polynomial (p j) base
  have hprod : (∏ j, d j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hd j)
  obtain ⟨u, hu, a, ha, he⟩ := exists_rational_direction_avoiding_levels base v hv U hU (∏ j, d j) hprod
  refine ⟨u, hu, a, ha, ?_⟩
  intro alpha hp hl j
  apply hfinite j ℝ alpha (fun i => (u i : ℝ))
  have h := he alpha hp hl
  rw [map_prod] at h
  exact Finset.prod_ne_zero_iff.mp h j (Finset.mem_univ j)

theorem exists_common_rational_direction_interval_near {σ : Type*} [Fintype σ]
    (p : σ → MvPolynomial ι ℝ) (base : ι)
    (hregular : ∃ b : ℝ, 0 < b ∧ ∀ alpha : ℝ, 0 < alpha → alpha < b → ∀ j (x : ι → ℝ),
      (p j).eval₂ (RingHom.id ℝ) x = alpha →
        Function.Surjective (fderiv ℝ (fun y => (p j).eval₂ (RingHom.id ℝ) y) x))
    (v : ι → ℝ) (hv : v base = 1) (U : Set (ι → ℝ)) (hU : U ∈ nhds v) :
    ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex base → ℚ,
      rationalDirection base u ∈ U ∧ ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
        ∀ j, {x : ι → ℝ | ∀ k, (Algebra.ProjectionEquations.system
          (Algebra.LevelProjectionSpecialization.levelPolynomial (p j) alpha) base k).eval₂ (RingHom.id ℝ)
            (Sum.elim x (rationalDirection base u)) = 0}.Finite := by
  obtain ⟨u, hu, a, ha, hfinite⟩ := exists_common_rational_extended_direction_near p base v hv U hU
  obtain ⟨b, hb, hreg⟩ := hregular
  refine ⟨u, hu, min a b, lt_min ha hb, ?_⟩
  intro alpha hp hl j
  apply finite_roots_of_extended _ base _ (rationalDirection_base base u)
    (hfinite alpha hp (hl.trans_le (min_le_left _ _)) j)
  intro x hx
  have heval (y : ι → ℝ) :
      (Algebra.LevelProjectionSpecialization.levelPolynomial (p j) alpha).eval₂ (RingHom.id ℝ) y =
        (p j).eval₂ (RingHom.id ℝ) y - alpha := by
    simp [Algebra.LevelProjectionSpecialization.levelPolynomial, eval₂_sub, eval₂_map, Algebra.algebraMap_self]
  rw [heval, sub_eq_zero] at hx
  have hr := hreg alpha hp (hl.trans_le (min_le_right _ _)) j x hx
  have hd : fderiv ℝ (fun y => (Algebra.LevelProjectionSpecialization.levelPolynomial (p j) alpha).eval₂ (RingHom.id ℝ) y) x =
      fderiv ℝ (fun y => (p j).eval₂ (RingHom.id ℝ) y) x := by
    simp_rw [heval]
    exact fderiv_sub_const alpha
  rw [hd]
  exact hr

end LeanCanny.Geometry.ProjectionCritical
