/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalRepresentationTransfer
public import LeanCanny.Algebra.ProjectionSystemCoordinates

/-! # Critical-point decoding in real and other extension fields

Representations over the algebraic closure decode soundly at parameter roots
in any extension field. Thus real roots of a base-field eliminant give real
regular critical points of the original hypersurface. Conversely, every regular critical point with algebraic coordinates has a
parameter root in its own field. No effective construction is asserted here.
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectionSystemCoordinates
open MvPolynomial ProjectionFiniteSpecialization FiniteSystemCoordinates

variable {K E ι : Type*} [Field K] [Field E] [Algebra K E] [Fintype ι]

theorem decodeOver_regular_point (p : MvPolynomial ι K) (base : ι) (u : DirectionIndex base → ℕ)
    (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure K) (equations p base u))
    (θ : E) (hθ : Polynomial.aeval θ r.polynomial = 0) :
    let x := fun i => r.decodeOver θ (some i)
    MvPolynomial.aeval x p = 0 ∧
      (∀ i, MvPolynomial.aeval x (pderiv i p) = normalizedDirection base (fun j => (u j : E)) i *
        MvPolynomial.aeval x (pderiv base p)) ∧ MvPolynomial.aeval x (pderiv base p) ≠ 0 :=
  regular_point_of_solution p base u (r.decodeOver θ) (r.decodeOver_sound θ hθ).1

theorem exists_regular_point_of_root (p : MvPolynomial ι K) (base : ι) (u : DirectionIndex base → ℕ)
    (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure K) (equations p base u))
    (hroot : ∃ θ : E, Polynomial.aeval θ r.polynomial = 0) :
    ∃ x : ι → E, MvPolynomial.aeval x p = 0 ∧
      (∀ i, MvPolynomial.aeval x (pderiv i p) = normalizedDirection base (fun j => (u j : E)) i *
        MvPolynomial.aeval x (pderiv base p)) ∧ MvPolynomial.aeval x (pderiv base p) ≠ 0 := by
  obtain ⟨θ, hθ⟩ := hroot
  exact ⟨fun i => r.decodeOver θ (some i), decodeOver_regular_point p base u r θ hθ⟩

noncomputable def reciprocalLift (p : MvPolynomial ι K) (base : ι) (x : ι → E) : Option ι → E :=
  fun j => j.elim ((MvPolynomial.aeval x (pderiv base p))⁻¹) x

omit [Fintype ι] in
theorem reciprocalLift_solution (p : MvPolynomial ι K) (base : ι) (u : DirectionIndex base → ℕ)
    (x : ι → E) (hp : MvPolynomial.aeval x p = 0)
    (hpartial : ∀ i, MvPolynomial.aeval x (pderiv i p) = normalizedDirection base (fun j => (u j : E)) i *
      MvPolynomial.aeval x (pderiv base p)) (hne : MvPolynomial.aeval x (pderiv base p) ≠ 0) :
    reciprocalLift p base x ∈ FiniteSystemCoordinates.zeroSet (L := E) (equations p base u) := by
  have hzx : (fun i => reciprocalLift p base x (some i)) = x := rfl
  intro j
  rw [eval_equations]
  rcases j with b | i
  · cases b
    · rw [GenericProjectionFinite.equation, GenericProjectionFinite.eval_liftPolynomial, hzx]
      exact hp
    · rw [GenericProjectionFinite.equation, map_sub, map_mul, aeval_X,
        GenericProjectionFinite.eval_liftPolynomial, hzx, map_one]
      exact sub_eq_zero.mpr (inv_mul_cancel₀ hne)
  · rw [GenericProjectionFinite.equation, map_sub, map_mul, aeval_C,
      GenericProjectionFinite.eval_liftPolynomial, GenericProjectionFinite.eval_liftPolynomial, hzx]
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using sub_eq_zero.mpr (hpartial i)

/-- Every regular critical point with algebraic coordinates is obtained from
an eliminant root in the same target field. -/
theorem parameter_of_algebraic_regular_point (p : MvPolynomial ι K) (base : ι) (u : DirectionIndex base → ℕ)
    (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure K) (equations p base u))
    (x : ι → E) (hp : MvPolynomial.aeval x p = 0)
    (hpartial : ∀ i, MvPolynomial.aeval x (pderiv i p) = normalizedDirection base (fun j => (u j : E)) i *
      MvPolynomial.aeval x (pderiv base p)) (hne : MvPolynomial.aeval x (pderiv base p) ≠ 0)
    (halg : ∀ i, IsAlgebraic K (x i)) :
    ∃ θ : E, Polynomial.aeval θ r.polynomial = 0 ∧ ∀ i, r.decodeOver θ (some i) = x i := by
  let z := reciprocalLift p base x
  have hz : z ∈ FiniteSystemCoordinates.zeroSet (L := E) (equations p base u) :=
    reciprocalLift_solution p base u x hp hpartial hne
  have hzalg : ∀ j, IsAlgebraic K (z j) := by
    intro j
    cases j with
    | none => exact (GenericProjectionFinite.algebraic_polynomial_value (B := K) (pderiv base p) x halg).inv
    | some i => exact halg i
  have hc := r.complete_at_algebraic_solution z hz hzalg
  exact ⟨AsymmetricProjection.projection r.direction z, hc.1, fun i => congrFun hc.2 (some i)⟩

end LeanCanny.Algebra.ProjectionSystemCoordinates
