/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeHomogenization
public import LeanCanny.Algebra.ReciprocalBounds

/-! # The actual tube projection system with reciprocal regularity

The inverse coordinate is at `none`; original point, direction and perturbation
coordinates retain their order at `some`. There is one additional equation.
All roots enforce nonzero base partial derivative and determine the inverse
uniquely. Degree and coefficient budgets are explicit in the compiled input size.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRegularSource
open Complexity LeanCanny.Encoding
open Geometry TubeEncoding TubeProjectionEncoding
open LeanCanny.Algebra

abbrev Variable (bits : List Bool) := Option (TubeSource.IntegerProjectionVariable bits)
abbrev Index (bits : List Bool) := Option (TubeSource.ProjectionIndex bits)

def base (n : ℕ) : TubeProjectionEncoding.Variable n := .inl (.inl (TubePolynomial.base (Fin n)))

noncomputable def polynomial (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) :
    Index bits → MvPolynomial (Variable bits) ℤ
  | none => ReciprocalEquation.polynomial (TubeSource.integerProjection bits s none) (base (CompactSource.term bits).arity)
  | some j => MvPolynomial.rename some (TubeSource.integerProjection bits s j)

def coefficientBudget (bits : List Bool) : ℕ :=
  TubeSource.massBudget (CompactSource.size bits) + TubeIndexed.degreeBound bits + 1

theorem coefficientBudget_unary : UnaryFn coefficientBudget :=
  (((((UnaryFn.const 20).mul (CompactSource.size_unary.pow_const 2)).add
    ((UnaryFn.const 6).mul CompactSource.size_unary)).add (UnaryFn.const 21)).add
      TubeIndexed.degreeBound_unary).add (UnaryFn.const 1)

theorem degree_le (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) (j : Index bits) :
    (polynomial bits s j).totalDegree ≤ TubeIndexed.degreeBound bits := by
  cases j with
  | none =>
    apply (ReciprocalEquation.degree_le _ _).trans
    apply max_le (TubeHomogenization.source_degree bits s none)
    unfold TubeIndexed.degreeBound
    omega
  | some j =>
    exact (MvPolynomial.totalDegree_rename_le _ _).trans (TubeHomogenization.source_degree bits s j)

theorem coefficient_bound (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) (j : Index bits)
    (e : Variable bits →₀ ℕ) : ((polynomial bits s j).coeff e).natAbs ≤ 2 ^ coefficientBudget bits := by
  have hb (i : TubeSource.ProjectionIndex bits) (m : TubeSource.IntegerProjectionVariable bits →₀ ℕ) :
      ((TubeSource.integerProjection bits s i).coeff m).natAbs ≤ 2 ^ TubeSource.massBudget (CompactSource.size bits) :=
    (MvMass.coeff_le _ _).trans (TubeSource.integer_projection_mass_le bits s i)
  cases j with
  | none => exact ReciprocalEquation.coefficient_pow_bound _ _ _ _ (TubeHomogenization.source_degree bits s none) (hb none) e
  | some j =>
    rw [polynomial, ReciprocalEquation.coefficient_rename]
    split_ifs
    · exact (hb j e.some).trans (Nat.pow_le_pow_right (by decide) (by unfold coefficientBudget; omega))
    · exact Nat.zero_le _

section Roots
variable {K : Type*} [Field K]

noncomputable def RegularRoot (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : ℤ →+* K) (x : TubeSource.IntegerProjectionVariable bits → K) : Prop :=
  (∀ j, (TubeSource.integerProjection bits s j).eval₂ φ x = 0) ∧
    (MvPolynomial.pderiv (base (CompactSource.term bits).arity) (TubeSource.integerProjection bits s none)).eval₂ φ x ≠ 0

theorem root_iff (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) (φ : ℤ →+* K)
    (x : TubeSource.IntegerProjectionVariable bits → K) (u : K) :
    (∀ j, (polynomial bits s j).eval₂ φ (fun i => i.elim u x) = 0) ↔
      RegularRoot bits s φ x ∧ u =
        ((MvPolynomial.pderiv (base (CompactSource.term bits).arity) (TubeSource.integerProjection bits s none)).eval₂ φ x)⁻¹ := by
  constructor
  · intro h
    have hi := (ReciprocalEquation.root_iff _ _ φ x u).mp (h none)
    refine ⟨⟨?_, hi.1⟩, hi.2⟩
    intro j
    have hp := h (some j)
    simpa only [polynomial, MvPolynomial.eval₂_rename, Function.comp_def, Option.elim_some] using hp
  · rintro ⟨⟨hp, hne⟩, hu⟩ j
    cases j with
    | none => exact (ReciprocalEquation.root_iff _ _ φ x u).mpr ⟨hne, hu⟩
    | some j => simpa only [polynomial, MvPolynomial.eval₂_rename, Function.comp_def, Option.elim_some] using hp j

theorem exists_lift_iff (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) (φ : ℤ →+* K)
    (x : TubeSource.IntegerProjectionVariable bits → K) :
    (∃ u, ∀ j, (polynomial bits s j).eval₂ φ (fun i => i.elim u x) = 0) ↔ RegularRoot bits s φ x := by
  simp only [root_iff]
  exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

end Roots
end LeanCanny.ETR.TubeRegularSource
