/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationSystem

/-!
# A single polynomial equation for arbitrary ETR formulas

The equation system is collapsed into a sum of squares only once, after all Boolean
structure has been compiled. Consequently each system term is copied exactly twice.
-/

@[expose] public section

namespace LeanCanny.ETR.Term

def sumSquares : List Term → Term
  | [] => .const 0
  | t :: ts => .add t.square (sumSquares ts)

theorem eval_sumSquares_nonneg (ts : List Term) (env : ℕ → ℝ) :
    0 ≤ (sumSquares ts).eval env := by
  induction ts with
  | nil => simp [sumSquares, eval]
  | cons t ts ih => exact add_nonneg (mul_self_nonneg _) ih

theorem eval_sumSquares_eq_zero_iff (ts : List Term) (env : ℕ → ℝ) :
    (sumSquares ts).eval env = 0 ↔ ∀ t ∈ ts, t.eval env = 0 := by
  induction ts with
  | nil => simp [sumSquares, eval]
  | cons t ts ih =>
      change t.eval env * t.eval env + (sumSquares ts).eval env = 0 ↔ _
      rw [List.forall_mem_cons]
      constructor
      · intro h
        have ht := mul_self_nonneg (t.eval env)
        have hs := eval_sumSquares_nonneg ts env
        have ht0 : t.eval env * t.eval env = 0 := by linarith
        have hs0 : (sumSquares ts).eval env = 0 := by linarith
        exact ⟨mul_self_eq_zero.mp ht0, ih.mp hs0⟩
      · rintro ⟨ht, hs⟩
        rw [ht, ih.mpr hs]
        norm_num

theorem sumSquares_scoped (ts : List Term) (n : ℕ) (h : ∀ t ∈ ts, t.arity ≤ n) :
    (sumSquares ts).arity ≤ n := by
  induction ts with
  | nil => exact Nat.zero_le _
  | cons t ts ih =>
      have ht := h t (List.mem_cons_self ..)
      have hs := ih (fun u hu => h u (List.mem_cons_of_mem t hu))
      simp only [sumSquares, square, arity]
      omega

end LeanCanny.ETR.Term

namespace LeanCanny.ETR.Formula

/-- The resulting single equation has integer coefficients and only existential variables. -/
def singleEquation (p : Formula) : Formula := .eqZero (Term.sumSquares p.equationSystem.terms)

theorem satisfiable_iff_singleEquation (p : Formula) :
    p.Satisfiable ↔ p.singleEquation.Satisfiable := by
  rw [p.satisfiable_iff_equationSystem]
  exact exists_congr (fun env => (Term.eval_sumSquares_eq_zero_iff _ env).symm)

theorem singleEquation_scoped (p : Formula) :
    p.singleEquation.arity ≤ p.equationSystem.next := by
  exact Term.sumSquares_scoped _ _ ((p.toSigned true).equations_scoped p.arity (by simp))

end LeanCanny.ETR.Formula
