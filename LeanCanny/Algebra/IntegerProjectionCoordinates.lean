/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerCoordinatePolynomials
public import LeanCanny.Algebra.CompleteProjectionCoordinates

/-! # Integer rational representations of regular critical points

For rational input polynomials, integer eliminants and integer coordinate
numerator/denominator pairs represent all regular critical points of certified
directions in any rational extension field, including the reals. Denominator
clearing preserves degrees and values; no coefficient-height or space bound
is obtained by this existence construction.
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectionAnnihilatorDirections
open ProjectionFiniteSpecialization ProjectionSystemCoordinates FiniteSystemCoordinates IntegerCoordinatePolynomials

variable {ι E : Type*} [Fintype ι] [Field E] [Algebra ℚ E]

namespace CertifiedDirection
variable {p : MvPolynomial ι ℚ} {base : ι} {u : DirectionIndex base → ℕ}

noncomputable def integerRegularRootEquiv (c : CertifiedDirection p base u)
    (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (equations p base u)) (d : IntegerData r) :
    {θ : E // Polynomial.aeval θ d.polynomial = 0} ≃ {x : ι → E // RegularPoint p base u x} :=
  d.rootEquiv.trans (c.regularRootEquiv r)

theorem exists_regularPoint_iff_integer (c : CertifiedDirection p base u)
    (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (equations p base u))
    (d : IntegerData r) (P : (ι → E) → Prop) :
    (∃ x : ι → E, RegularPoint p base u x ∧ P x) ↔
      ∃ θ : E, Polynomial.aeval θ d.polynomial = 0 ∧ P (fun i => d.decode θ (some i)) := by
  simpa only [d.root_iff (E := E), d.decode_eq (E := E)] using c.exists_regularPoint_iff r P

end CertifiedDirection

theorem exists_integer_family {σ : Type*} [Fintype σ] (p : σ → MvPolynomial ι ℚ) (base : ι) :
    ∃ b : ℕ, ∃ u : DirectionIndex base → ℕ, (∀ i, u i ≤ b) ∧
      ∀ t, Nonempty (CertifiedDirection (p t) base u ×
        (Σ r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (equations (p t) base u), IntegerData r)) := by
  obtain ⟨b, u, hu, hc⟩ := ProjectionAnnihilatorDirections.exists_family_representations p base
  refine ⟨b, u, hu, ?_⟩
  intro t
  obtain ⟨cr⟩ := hc t
  obtain ⟨d⟩ := nonempty_integerData cr.2
  exact ⟨(cr.1, ⟨cr.2, d⟩)⟩

end LeanCanny.Algebra.ProjectionAnnihilatorDirections
