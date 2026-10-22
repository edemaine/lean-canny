/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CriticalValueAnnihilator
public import LeanCanny.Geometry.PolynomialCalculus
public import LeanCanny.Geometry.CriticalEnergyPolynomial

/-! # Finite critical values of the specialized perturbation energy

The algebraic critical-value theorem applies to real polynomial evaluation and
its analytic derivative. Specializing the perturbation parameters produces a
polynomial in the spatial variables, so every active energy has finitely many
critical values at each fixed epsilon.
-/

@[expose] public section

namespace LeanCanny.Geometry.PolynomialCalculus

theorem finite_critical_values {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) :
    {c : ℝ | ∃ x : ι → ℝ, fderiv ℝ (fun y => MvPolynomial.aeval y p) x = 0 ∧
      MvPolynomial.aeval x p = c}.Finite := by
  classical
  apply (Algebra.CriticalValueAnnihilator.finite_critical_values p).subset
  rintro c ⟨x, hx, hv⟩
  refine ⟨x, ?_, hv⟩
  exact (critical_iff (algebraMap ℝ ℝ) p x).mp hx

end LeanCanny.Geometry.PolynomialCalculus

namespace LeanCanny.Geometry.PolynomialPerturbation
open MvPolynomial

variable {ι : Type*}

noncomputable def spatialAssignment (epsilon delta : ℝ) (a : Constraint ι → ℝ) :
    Variable ι → MvPolynomial ι ℝ
  | .inl false => C epsilon
  | .inl true => C delta
  | .inr (.inl i) => X i
  | .inr (.inr i) => C (a i)

noncomputable def spatialPolynomial (q : MvPolynomial (Variable ι) ℤ) (epsilon delta : ℝ)
    (a : Constraint ι → ℝ) : MvPolynomial ι ℝ :=
  q.eval₂ (Int.castRingHom _) (spatialAssignment epsilon delta a)

theorem eval_spatialPolynomial (q : MvPolynomial (Variable ι) ℤ) (epsilon delta : ℝ)
    (a : Constraint ι → ℝ) (x : ι → ℝ) :
    aeval x (spatialPolynomial q epsilon delta a) =
      q.eval₂ (Int.castRingHom ℝ) (assignment epsilon delta (x, a)) := by
  change (aeval x).toRingHom (q.eval₂ (Int.castRingHom _) (spatialAssignment epsilon delta a)) = _
  rw [MvPolynomial.hom_eval₂, RingHom.eq_intCast' ((aeval x).toRingHom.comp (Int.castRingHom (MvPolynomial ι ℝ)))]
  congr 1
  funext v
  rcases v with b | v
  · cases b <;> simp [spatialAssignment, assignment]
  · rcases v with i | i <;> simp [spatialAssignment, assignment]

variable [Fintype ι]

theorem finite_energy_critical_values (p : MvPolynomial ι ℤ) (s : Finset (Constraint ι)) (epsilon : ℝ) :
    {c : ℝ | ∃ x : ι → ℝ, fderiv ℝ (ActiveRadius.energy (constraintMap p epsilon) s) x = 0 ∧
      ActiveRadius.energy (constraintMap p epsilon) s x = c}.Finite := by
  have h := PolynomialCalculus.finite_critical_values (spatialPolynomial (energyPolynomial p s) epsilon 0 0)
  simpa only [eval_spatialPolynomial, eval_energyPolynomial] using h

end LeanCanny.Geometry.PolynomialPerturbation
