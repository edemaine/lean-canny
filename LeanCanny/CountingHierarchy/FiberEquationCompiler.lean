/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CompiledRationalSource
public import LeanCanny.CountingHierarchy.EncodedTermPolynomial

/-! # The native equation compiler preserves every reserved real parameter -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open LeanCanny.Encoding LeanCanny.Encoding.Brackets LeanCanny.ETR

/-- The compiled equation is the actual sum of squares of the native compiler's
output, before quantifying any original variable. -/
theorem compiledTerm_encode_eq (p : Formula) :
    TermView.term (RationalSubstitutionBits.compiledTerm p.encode) =
      SumSquares.accumulate ((p.toSigned true).equations (p.nnf true).encode.length).terms (.const 0) := by
  rw [RationalSubstitutionBits.compiledTerm, Function.comp_apply, EquationCompiler.toSingleEquation,
    EquationCompiler.compileTerms_encode, EquationList.toSingleEquation_listBits]
  simp only [NNF.second, Formula.encode, Formula.toData, remainingChildren_toBits, firstChild_toBits,
    TermView.term_toBits]

/-- Satisfying assignments in a fixed prefix fiber extend to solutions of the
compiled equation in the same fiber. The reverse implication uses the original
formula's semantics directly; no expanded polynomial is assumed. -/
theorem compiledTerm_prefix_fiber_iff (p : Formula) (r : ℕ)
    (hr : r ≤ (p.nnf true).encode.length) (x : Fin r → ℝ) :
    (∃ env : ℕ → ℝ, (∀ i : Fin r, env i.val = x i) ∧ p.Holds env) ↔
      ∃ env : ℕ → ℝ, (∀ i : Fin r, env i.val = x i) ∧
        (TermView.term (RationalSubstitutionBits.compiledTerm p.encode)).eval env = 0 := by
  rw [compiledTerm_encode_eq]
  have ha : (p.toSigned true).arity ≤ (p.nnf true).encode.length := by
    simpa only [Formula.toSigned_arity, Formula.nnf_arity, Formula.encode, Data.length_toBits] using
      (p.nnf true).arity_le_dataSize
  constructor
  · rintro ⟨env, hprefix, hp⟩
    obtain ⟨env', hpreserve, heq⟩ := (p.toSigned true).equations_complete (p.nnf true).encode.length ha env
      ((p.holds_toSigned true env).mpr hp)
    refine ⟨env', fun i => (hpreserve i.val (i.isLt.trans_le hr)).symm.trans (hprefix i), ?_⟩
    exact (SumSquares.accumulate_zero_iff _ _).mpr heq
  · rintro ⟨env, hprefix, heq⟩
    exact ⟨env, hprefix, (p.holds_toSigned true env).mp
      ((p.toSigned true).equations_sound _ env ((SumSquares.accumulate_zero_iff _ _).mp heq))⟩

end LeanCanny.CountingHierarchy
