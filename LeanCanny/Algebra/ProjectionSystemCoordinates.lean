/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteSystemCoordinates
public import LeanCanny.Algebra.ProjectionFiniteSpecialization

/-! # Rational coordinates for integer-direction critical projection systems

Choose an integer direction outside the exceptional polynomial of a regular
projection system. Its full extended zero set is finite over the algebraic
closure, and therefore has a rational univariate representation over the input
field. The exceptional polynomial's degree and the representation's coefficient
sizes still lack input-size bounds.
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectionSystemCoordinates
open MvPolynomial ProjectionFiniteSpecialization FiniteSystemCoordinates

variable {K ι : Type*} [Field K]

noncomputable def equations (p : MvPolynomial ι K) (base : ι) (u : DirectionIndex base → ℕ) :
    Sum Bool ι → MvPolynomial (Option ι) K :=
  GenericProjectionFinite.equation p base (normalizedDirection base (fun i => (u i : K)))

section Extension
variable {L : Type*} [Field L] [Algebra K L]

private theorem eval_nat_ne_zero {σ : Type*} (d : MvPolynomial σ K) (u : σ → ℕ)
    (he : MvPolynomial.eval (fun i => (u i : K)) d ≠ 0) :
    MvPolynomial.eval₂ (algebraMap K L) (fun i => (u i : L)) d ≠ 0 := by
  have hmap := MvPolynomial.eval₂_comp_left (algebraMap K L)
    (RingHom.id K) (fun i => (u i : K)) d
  rw [MvPolynomial.eval₂_id] at hmap
  have hn := (algebraMap K L).injective.ne he
  rw [hmap] at hn
  simpa only [RingHom.comp_id, Function.comp_def, map_natCast, map_zero] using hn

theorem map_normalizedDirection (base : ι) (u : DirectionIndex base → ℕ) :
    (fun i => algebraMap K L (normalizedDirection base (fun j => (u j : K)) i)) =
      normalizedDirection base (fun j => (u j : L)) := by
  classical
  funext i
  by_cases hi : i = base <;> simp [normalizedDirection, hi]

theorem map_equations (p : MvPolynomial ι K) (base : ι) (u : DirectionIndex base → ℕ) (j : Sum Bool ι) :
    (equations p base u j).map (algebraMap K L) =
      GenericProjectionFinite.equation p base (normalizedDirection base (fun i => (u i : L))) j := by
  rw [equations, ProjectionFiniteSpecialization.map_equation, map_normalizedDirection]

theorem eval_equations (p : MvPolynomial ι K) (base : ι) (u : DirectionIndex base → ℕ)
    (z : Option ι → L) (j : Sum Bool ι) :
    MvPolynomial.eval₂ (algebraMap K L) z (equations p base u j) =
      MvPolynomial.aeval z (GenericProjectionFinite.equation p base
        (normalizedDirection base (fun i => (u i : L))) j) := by
  rw [← MvPolynomial.eval_map, map_equations]
  rfl

/-- Discarding the reciprocal variable gives an actual regular critical point. -/
theorem regular_point_of_solution (p : MvPolynomial ι K) (base : ι) (u : DirectionIndex base → ℕ)
    (z : Option ι → L) (hz : z ∈ FiniteSystemCoordinates.zeroSet (L := L) (equations p base u)) :
    let x := fun i => z (some i)
    MvPolynomial.aeval x p = 0 ∧
      (∀ i, MvPolynomial.aeval x (pderiv i p) = normalizedDirection base (fun j => (u j : L)) i *
        MvPolynomial.aeval x (pderiv base p)) ∧ MvPolynomial.aeval x (pderiv base p) ≠ 0 := by
  have he (j : Sum Bool ι) : MvPolynomial.aeval z (GenericProjectionFinite.equation p base
      (normalizedDirection base (fun i => (u i : L))) j) = 0 := by
    rw [← eval_equations]
    exact hz j
  have hp := he (.inl false)
  rw [GenericProjectionFinite.equation, GenericProjectionFinite.eval_liftPolynomial] at hp
  have hinv : z none * MvPolynomial.aeval (fun i => z (some i)) (pderiv base p) = 1 := by
    have h := he (.inl true)
    rw [GenericProjectionFinite.equation, map_sub, map_mul, aeval_X,
      GenericProjectionFinite.eval_liftPolynomial, map_one] at h
    exact sub_eq_zero.mp h
  refine ⟨hp, ?_, ?_⟩
  · intro i
    have h := he (.inr i)
    rw [GenericProjectionFinite.equation, map_sub, map_mul, aeval_C,
      GenericProjectionFinite.eval_liftPolynomial, GenericProjectionFinite.eval_liftPolynomial] at h
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using sub_eq_zero.mp h
  · intro hzero
    rw [hzero, mul_zero] at hinv
    exact zero_ne_one hinv

end Extension

/-- Qualitative integer choices already suffice over the full algebraic closure,
not merely for solutions in the coefficient field. -/
theorem exists_representation [Fintype ι] [CharZero K] (p : MvPolynomial ι K) (base : ι) :
    ∃ b : ℕ, ∃ u : DirectionIndex base → ℕ, (∀ i, u i ≤ b) ∧
      Nonempty (FiniteSystemCoordinates.Representation (L := AlgebraicClosure K) (equations p base u)) := by
  obtain ⟨d, hd, hfinite⟩ := ProjectionFiniteSpecialization.exists_exceptional_polynomial p base
  obtain ⟨u, hu, he⟩ := PolynomialGridAvoidance.exists_nat_eval_ne_zero d hd d.totalDegree le_rfl
  refine ⟨d.totalDegree, u, hu, ?_⟩
  have heL := eval_nat_ne_zero (L := AlgebraicClosure K) d u he
  have hfin := hfinite (AlgebraicClosure K) (fun i => (u i : AlgebraicClosure K)) heL
  apply FiniteSystemCoordinates.nonempty_algebraicClosure_representation
  apply hfin.subset
  intro z hz j
  rw [← eval_equations]
  exact hz j

/-- One common integer direction works for a whole finite family of surfaces. -/
theorem exists_family_representations [Fintype ι] [CharZero K]
    {σ : Type*} [Fintype σ] (p : σ → MvPolynomial ι K) (base : ι) :
    ∃ b : ℕ, ∃ u : DirectionIndex base → ℕ, (∀ i, u i ≤ b) ∧
      ∀ r, Nonempty (FiniteSystemCoordinates.Representation (L := AlgebraicClosure K) (equations (p r) base u)) := by
  classical
  choose d hd hf using fun r => ProjectionFiniteSpecialization.exists_exceptional_polynomial (p r) base
  obtain ⟨u, hu, he⟩ := PolynomialGridAvoidance.exists_nat_common_nonzero d hd
    (∑ r, (d r).totalDegree) le_rfl
  refine ⟨∑ r, (d r).totalDegree, u, hu, ?_⟩
  intro r
  have heL := eval_nat_ne_zero (L := AlgebraicClosure K) (d r) u (he r)
  have hfin := hf r (AlgebraicClosure K) (fun i => (u i : AlgebraicClosure K)) heL
  apply FiniteSystemCoordinates.nonempty_algebraicClosure_representation
  apply hfin.subset
  intro z hz j
  rw [← eval_equations]
  exact hz j

/-- Every eliminant root decodes to a regular critical point of the original
surface after discarding the reciprocal coordinate. -/
theorem decode_regular_point {L : Type*} [Field L] [Algebra K L] [Fintype ι] (p : MvPolynomial ι K) (base : ι) (u : DirectionIndex base → ℕ)
    (r : FiniteSystemCoordinates.Representation (L := L) (equations p base u))
    (θ : L) (hθ : Polynomial.aeval θ r.polynomial = 0) :
    let x := fun i => r.decode θ (some i)
    MvPolynomial.aeval x p = 0 ∧
      (∀ i, MvPolynomial.aeval x (pderiv i p) = normalizedDirection base (fun j => (u j : L)) i *
        MvPolynomial.aeval x (pderiv base p)) ∧ MvPolynomial.aeval x (pderiv base p) ≠ 0 :=
  regular_point_of_solution p base u (r.decode θ) (r.decode_of_root θ hθ).1

end LeanCanny.Algebra.ProjectionSystemCoordinates
