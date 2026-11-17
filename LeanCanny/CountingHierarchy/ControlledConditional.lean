/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled

/-! # Native conditionals with uniform controlled-family budgets -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

noncomputable def conditional {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P Q : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (CP : Controlled P enc a) (CQ : Controlled Q enc a) (b : α → Bool)
    (hb : ComputableInPolyTime b enc encBool) :
    Controlled (fun w => if b w then P w else Q w) enc a where
  arity_computable := CP.arity_computable
  degreeBound w := max (CP.degreeBound w) (CQ.degreeBound w)
  degree_computable := ComputableInPolyTime.binary_max' CP.degree_computable CQ.degree_computable
  degree_le w := by
    cases b w
    · exact (CQ.degree_le w).trans (le_max_right _ _)
    · exact (CP.degree_le w).trans (le_max_left _ _)
  massExponent w := max (CP.massExponent w) (CQ.massExponent w)
  mass_computable := ComputableInPolyTime.binary_max' CP.mass_computable CQ.mass_computable
  mass_le w := by
    cases b w
    · exact (CQ.mass_le w).trans (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
    · exact (CP.mass_le w).trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  cutoff w := max (CP.cutoff w) (CQ.cutoff w)
  cutoff_computable := ComputableInPolyTime.binary_max' CP.cutoff_computable CQ.cutoff_computable
  evaluate q := if b q.1 then CP.evaluate q else CQ.evaluate q
  evaluate_mem := CountingFunction.ite
    (CountingFunction.of_polyTime (hb.comp (ComputableInPolyTime.fst _ _))) CP.evaluate_mem CQ.evaluate_mem
  evaluate_eq w p z hp hc := by
    cases b w
    · exact CQ.evaluate_eq w p z hp ((le_max_right _ _).trans_lt hc)
    · exact CP.evaluate_eq w p z hp ((le_max_left _ _).trans_lt hc)

end LeanCanny.CountingHierarchy.Controlled
