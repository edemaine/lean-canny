/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationSize
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Degree bounds for the single-equation normalization

The polynomial represented by the normalized expression has total degree at most
four times the original bit length. This connects the syntax-size accounting with
Mathlib's actual multivariate polynomials, without expanding them computationally.
-/

@[expose] public section

namespace LeanCanny.ETR

namespace Term

/-- An upper bound on total degree, allowing cancellation of leading terms. -/
def degreeBound : Term → ℕ
  | .const _ => 0
  | .var _ => 1
  | .add t u => max t.degreeBound u.degreeBound
  | .mul t u => t.degreeBound + u.degreeBound

theorem totalDegree_toPolynomial_le (t : Term) : t.toPolynomial.totalDegree ≤ t.degreeBound := by
  induction t with
  | const z => exact (MvPolynomial.totalDegree_C z).le
  | var i => simp [toPolynomial, degreeBound]
  | add t u iht ihu =>
      exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max iht ihu)
  | mul t u iht ihu =>
      exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add iht ihu)

theorem degreeBound_le_dataSize (t : Term) : t.degreeBound ≤ t.toData.size := by
  induction t with
  | const z => exact Nat.zero_le _
  | var i => simp [degreeBound]
  | add t u iht ihu => simp only [degreeBound, dataSize_add]; omega
  | mul t u iht ihu => simp only [degreeBound, dataSize_mul]; omega

theorem degreeBound_sumSquares_le (ts : List Term) (degree : ℕ)
    (h : ∀ t ∈ ts, t.degreeBound ≤ degree) : (sumSquares ts).degreeBound ≤ 2 * degree := by
  induction ts with
  | nil => simp [sumSquares, degreeBound]
  | cons t ts ih =>
      have ht := h t (List.mem_cons_self ..)
      have hs := ih (fun u hu => h u (List.mem_cons_of_mem t hu))
      simp only [sumSquares, square, degreeBound]
      omega

end Term

namespace SignedFormula

theorem equations_degree_le (p : SignedFormula) (start : ℕ) :
    ∀ t ∈ (p.equations start).terms, t.degreeBound ≤ 2 * p.budget := by
  induction p generalizing start with
  | truth => simp [equations]
  | falsum => simp [equations, Term.degreeBound]
  | eqZero t | neZero t | ltZero t | nonneg t =>
      have ht := t.degreeBound_le_dataSize
      simp only [equations, List.forall_mem_singleton, Term.nonzeroEquation,
        Term.negativeEquation, Term.nonnegativeEquation, Term.square, Term.degreeBound, budget]
      omega
  | and p q ihp ihq =>
      simp only [equations, EquationSystem.conjunction, List.forall_mem_append, budget]
      constructor
      · intro t ht
        have := ihp start t ht
        omega
      · intro t ht
        have := ihq (p.equations start).next t ht
        omega
  | or p q ihp ihq =>
      simp only [equations, EquationSystem.disjunction, List.forall_mem_cons,
        List.forall_mem_append, List.forall_mem_map, budget]
      constructor
      · simp only [Term.booleanEquation, Term.degreeBound]
        omega
      constructor
      · intro t ht
        have := ihp start t ht
        simp only [Term.degreeBound]
        omega
      · intro t ht
        have := ihq (p.equations start).next t ht
        simp only [Term.oneMinus, Term.degreeBound]
        omega

end SignedFormula

namespace Formula

/-- The actual integer multivariate polynomial represented by the compiled single equation. -/
noncomputable def equationPolynomial (p : Formula) : MvPolynomial ℕ ℤ :=
  (Term.sumSquares p.equationSystem.terms).toPolynomial

theorem satisfiable_iff_equationPolynomial (p : Formula) :
    p.Satisfiable ↔ ∃ env : ℕ → ℝ,
      MvPolynomial.eval₂ (Int.castRingHom ℝ) env p.equationPolynomial = 0 := by
  simpa only [equationPolynomial, Term.eval₂_toPolynomial, Formula.Satisfiable,
    singleEquation, Holds] using p.satisfiable_iff_singleEquation

theorem equationPolynomial_totalDegree_le (p : Formula) :
    p.equationPolynomial.totalDegree ≤ 4 * p.inputSize := by
  have ht := Term.degreeBound_sumSquares_le p.equationSystem.terms
    (2 * (p.toSigned true).budget) ((p.toSigned true).equations_degree_le p.arity)
  have hb := p.toSigned_budget_le true
  have hd := (Term.sumSquares p.equationSystem.terms).totalDegree_toPolynomial_le
  rw [p.inputSize_eq_dataSize]
  exact hd.trans (by omega)

end Formula
end LeanCanny.ETR
