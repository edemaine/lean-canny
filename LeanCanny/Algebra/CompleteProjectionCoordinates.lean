/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectionAnnihilatorDirections
public import LeanCanny.Algebra.ProjectionCoordinateTransfer

/-! # Complete rational coordinates for certified critical systems

The retained annihilators prove that all solution coordinates are algebraic in
every target extension. Rational decoding is consequently both sound and
complete in that target, including the reals. Eliminant roots are in bijection
with regular critical points after discarding the uniquely determined reciprocal.
This remains a qualitative construction without input-size or workspace bounds.
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectionSystemCoordinates
open MvPolynomial ProjectionFiniteSpecialization FiniteSystemCoordinates

variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]

def RegularPoint (p : MvPolynomial ι K) (base : ι) (u : DirectionIndex base → ℕ) (x : ι → E) : Prop :=
  MvPolynomial.aeval x p = 0 ∧
    (∀ i, MvPolynomial.aeval x (pderiv i p) = normalizedDirection base (fun j => (u j : E)) i *
      MvPolynomial.aeval x (pderiv base p)) ∧ MvPolynomial.aeval x (pderiv base p) ≠ 0

theorem reciprocalLift_eq_solution (p : MvPolynomial ι K) (base : ι) (u : DirectionIndex base → ℕ)
    (z : Option ι → E) (hz : z ∈ FiniteSystemCoordinates.zeroSet (L := E) (equations p base u)) :
    reciprocalLift p base (fun i => z (some i)) = z := by
  have h := hz (.inl true)
  rw [eval_equations, GenericProjectionFinite.equation, map_sub, map_mul, aeval_X,
    GenericProjectionFinite.eval_liftPolynomial, map_one] at h
  have hinv := eq_inv_of_mul_eq_one_left (sub_eq_zero.mp h)
  funext j
  cases j with
  | none => exact hinv.symm
  | some i => rfl

noncomputable def extendedRegularEquiv (p : MvPolynomial ι K) (base : ι) (u : DirectionIndex base → ℕ) :
    FiniteSystemCoordinates.zeroSet (L := E) (equations p base u) ≃ {x : ι → E // RegularPoint p base u x} where
  toFun z := ⟨fun i => z.val (some i), regular_point_of_solution p base u z.val z.property⟩
  invFun x := ⟨reciprocalLift p base x.val, reciprocalLift_solution p base u x.val x.property.1 x.property.2.1 x.property.2.2⟩
  left_inv z := Subtype.ext (reciprocalLift_eq_solution p base u z.val z.property)
  right_inv _x := Subtype.ext rfl

end LeanCanny.Algebra.ProjectionSystemCoordinates

namespace LeanCanny.Algebra.ProjectionAnnihilatorDirections
open ProjectionFiniteSpecialization ProjectionSystemCoordinates FiniteSystemCoordinates

variable {K E ι : Type*} [Field K] [Field E] [Algebra K E] [Fintype ι]

namespace CertifiedDirection
variable {p : MvPolynomial ι K} {base : ι} {u : DirectionIndex base → ℕ}

theorem complete_at_solution (c : CertifiedDirection p base u)
    (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure K) (equations p base u))
    (z : Option ι → E) (hz : z ∈ FiniteSystemCoordinates.zeroSet (L := E) (equations p base u)) :
    Polynomial.aeval (AsymmetricProjection.projection r.direction z) r.polynomial = 0 ∧
      r.decodeOver (AsymmetricProjection.projection r.direction z) = z :=
  r.complete_at_algebraic_solution z hz (c.algebraic_coordinates z hz)

/-- Unlike the generic transfer equivalence, the target field need not be algebraic. -/
noncomputable def rootEquivOver (c : CertifiedDirection p base u)
    (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure K) (equations p base u)) :
    {θ : E // Polynomial.aeval θ r.polynomial = 0} ≃
      FiniteSystemCoordinates.zeroSet (L := E) (equations p base u) where
  toFun θ := ⟨r.decodeOver θ.val, (r.decodeOver_sound θ.val θ.property).1⟩
  invFun z := ⟨AsymmetricProjection.projection r.direction z.val, (c.complete_at_solution r z.val z.property).1⟩
  left_inv θ := Subtype.ext (r.decodeOver_sound θ.val θ.property).2.1
  right_inv z := Subtype.ext (c.complete_at_solution r z.val z.property).2

noncomputable def regularRootEquiv (c : CertifiedDirection p base u)
    (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure K) (equations p base u)) :
    {θ : E // Polynomial.aeval θ r.polynomial = 0} ≃ {x : ι → E // RegularPoint p base u x} :=
  (c.rootEquivOver r).trans (extendedRegularEquiv p base u)

/-- Any predicate on regular critical points can be checked on decoded parameter roots. -/
theorem exists_regularPoint_iff (c : CertifiedDirection p base u)
    (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure K) (equations p base u)) (P : (ι → E) → Prop) :
    (∃ x : ι → E, RegularPoint p base u x ∧ P x) ↔
      ∃ θ : E, Polynomial.aeval θ r.polynomial = 0 ∧ P (fun i => r.decodeOver θ (some i)) := by
  constructor
  · rintro ⟨x, hx, hP⟩
    let e := c.regularRootEquiv (E := E) r
    let θ := e.symm ⟨x, hx⟩
    refine ⟨θ.val, θ.property, ?_⟩
    have he : (fun i => r.decodeOver θ.val (some i)) = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
    rwa [he]
  · rintro ⟨θ, hθ, hP⟩
    exact ⟨fun i => r.decodeOver θ (some i), decodeOver_regular_point p base u r θ hθ, hP⟩

end CertifiedDirection

/-- One common integer direction has complete base-field representations for
every surface in a finite family, valid in every target extension field. -/
theorem exists_family_representations [CharZero K]
    {σ : Type*} [Fintype σ] (p : σ → MvPolynomial ι K) (base : ι) :
    ∃ b : ℕ, ∃ u : DirectionIndex base → ℕ, (∀ i, u i ≤ b) ∧
      ∀ t, Nonempty (CertifiedDirection (p t) base u ×
        FiniteSystemCoordinates.Representation (L := AlgebraicClosure K) (equations (p t) base u)) := by
  obtain ⟨b, u, hu, hc⟩ := exists_family_certified_directions p base
  refine ⟨b, u, hu, ?_⟩
  intro t
  obtain ⟨c⟩ := hc t
  obtain ⟨r⟩ := c.nonempty_representation
  exact ⟨(c, r)⟩

end LeanCanny.Algebra.ProjectionAnnihilatorDirections
