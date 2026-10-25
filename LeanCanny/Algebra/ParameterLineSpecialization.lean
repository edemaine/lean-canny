/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialGridAvoidance
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Integer parameter lines avoiding a polynomial exceptional set

Retain one variable as a level parameter and specialize the remaining ones to
integers. A nonzero polynomial has such a line on which it remains nonzero;
the integer coordinates and the univariate degree are bounded by its total
degree. This does not provide an input-size bound for that total degree.
-/

@[expose] public section

namespace LeanCanny.Algebra.ParameterLineSpecialization
open MvPolynomial

variable {K σ : Type*} [Field K]

noncomputable def lineHom (u : σ → K) :
    MvPolynomial (Option σ) K →+* Polynomial K :=
  (Polynomial.mapRingHom (MvPolynomial.eval u)).comp (optionEquivLeft K σ).toRingHom

theorem lineHom_apply (u : σ → K) (p : MvPolynomial (Option σ) K) :
    lineHom u p = (optionEquivLeft K σ p).map (MvPolynomial.eval u) := rfl

@[simp] theorem lineHom_C (u : σ → K) (c : K) : lineHom u (C c) = Polynomial.C c := by
  simp [lineHom, optionEquivLeft_C]

@[simp] theorem lineHom_X_none (u : σ → K) : lineHom u (X none) = Polynomial.X := by
  simp [lineHom, optionEquivLeft_X_none]

@[simp] theorem lineHom_X_some (u : σ → K) (i : σ) :
    lineHom u (X (some i)) = Polynomial.C (u i) := by
  simp [lineHom, optionEquivLeft_X_some]

/-- Specialization of a line commutes with extension of the coefficient field. -/
theorem aeval_line {L : Type*} [Field L] [Algebra K L]
    (u : σ → K) (p : MvPolynomial (Option σ) K) (a : L) :
    Polynomial.aeval a (lineHom u p) =
      p.eval₂ (algebraMap K L) (fun i => i.elim a (fun j => algebraMap K L (u j))) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | mul_X p i hp =>
    cases i <;> simp only [map_mul, lineHom_X_none, lineHom_X_some,
      Polynomial.aeval_X, Polynomial.aeval_C,
      eval₂_mul, eval₂_X, hp, Option.elim_none, Option.elim_some]

theorem natDegree_line_le (u : σ → K) (p : MvPolynomial (Option σ) K) :
    (lineHom u p).natDegree ≤ p.totalDegree := by
  calc
    _ ≤ (optionEquivLeft K σ p).natDegree := Polynomial.natDegree_map_le
    _ = p.degreeOf none := natDegree_optionEquivLeft K p
    _ ≤ p.totalDegree := degreeOf_le_totalDegree p none

/-- Fixing integer coordinates leaves a nonzero univariate level polynomial.
Choosing a nonzero point on a joint grid proves the whole line is nonzero. -/
theorem exists_nat_line_nonzero [CharZero K] [Finite σ]
    (p : MvPolynomial (Option σ) K) (hp : p ≠ 0) :
    ∃ u : σ → ℕ, (∀ i, u i ≤ p.totalDegree) ∧
      lineHom (fun i => (u i : K)) p ≠ 0 ∧
      (lineHom (fun i => (u i : K)) p).natDegree ≤ p.totalDegree := by
  obtain ⟨w, hw, he⟩ := PolynomialGridAvoidance.exists_nat_eval_ne_zero p hp p.totalDegree le_rfl
  let u : σ → ℕ := fun i => w (some i)
  refine ⟨u, fun i => hw (some i), ?_, natDegree_line_le _ _⟩
  intro hz
  have hfun : (fun i : Option σ => (w i : K)) =
      (fun i => i.elim (w none : K) (fun j => (u j : K))) := by
    funext i
    cases i <;> rfl
  apply he
  rw [hfun, optionEquivLeft_elim_eval]
  change Polynomial.eval (w none : K) (lineHom (fun i => (u i : K)) p) = 0
  rw [hz, Polynomial.eval_zero]

end LeanCanny.Algebra.ParameterLineSpecialization
