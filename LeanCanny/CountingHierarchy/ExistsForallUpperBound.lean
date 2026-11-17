/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ExistsForallLanguage
public import LeanCanny.CountingHierarchy.FinitePrefixFiber
public import LeanCanny.CountingHierarchy.ControlledConditional
public import LeanCanny.CountingHierarchy.ControlledTwoBlockDecision
public import LeanCanny.ETR.Complexity

/-! # The encoded existential-universal theory of the reals in C₆₀P

Integer polynomial terms and arbitrary Boolean matrices are accepted. The outer
real block has a unary length, the remaining variables are universally quantified,
and malformed binary inputs are rejected. All source polynomials and their
modular evaluators are constructed by the native equation compiler.
-/

public section

namespace LeanCanny.CountingHierarchy.ExistsForall

open LeanCanny LeanCanny.ETR Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial
open scoped Classical

noncomputable def counterexample (w : List Bool) :
    MvPolynomial (Fin ((TermEvaluation.arity source w - parameterCount w) + parameterCount w)) ℤ :=
  reservedPrefixPolynomial (TermEvaluation.polynomial source w) (parameterCount_lt_arity w).le

noncomputable def guardedCounterexample (w : List Bool) :
    MvPolynomial (Fin ((TermEvaluation.arity source w - parameterCount w) + parameterCount w)) ℤ :=
  if frameFlag w then counterexample w else MvPolynomial.C 0

theorem counterexample_fiber (w : List Bool) (x : Fin (parameterCount w) → ℝ) :
    (∃ z : Fin (TermEvaluation.arity source w - parameterCount w) → ℝ,
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) (counterexample w) = 0) ↔
    ∃ env : ℕ → ℝ, (∀ i : Fin (parameterCount w), env i.val = x i) ∧ ¬(matrix w).Holds env := by
  rw [source_parameterCount_fiber_iff]
  exact (term_prefix_fiber_iff_finite (TermView.term (source w))
    (by rw [TermEvaluation.arity_eq]; exact Term.arity_le_dataSize _)
    (parameterCount_lt_arity w).le x).symm

theorem counterexample_avoidance (w : List Bool) :
    (∃ x : Fin (parameterCount w) → ℝ,
      ∀ z : Fin (TermEvaluation.arity source w - parameterCount w) → ℝ,
        MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) (counterexample w) ≠ 0) ↔
      SentenceHolds (parameterCount w) (matrix w) := by
  apply exists_congr
  intro x
  rw [← not_exists, counterexample_fiber]
  simp only [not_exists, not_and, not_not]

theorem guardedCounterexample_avoidance (w : List Bool) :
    w ∈ language ↔ ∃ x : Fin (parameterCount w) → ℝ,
      ∀ z : Fin (TermEvaluation.arity source w - parameterCount w) → ℝ,
        MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) (guardedCounterexample w) ≠ 0 := by
  rw [language_iff_normalized, frameFlag_iff]
  cases hf : frameFlag w
  · simp only [Bool.false_eq_true, false_and]
    constructor
    · exact False.elim
    · rintro ⟨x, hx⟩
      apply hx (fun _ => 0)
      simp [guardedCounterexample, hf]
  · simpa only [guardedCounterexample, hf, ↓reduceIte, and_true, true_and] using
      (counterexample_avoidance w).symm

attribute [local irreducible] TermEvaluation.controlled TermEvaluation.polynomial

noncomputable def controlledCounterexample : Controlled counterexample encBits 0 :=
  (TermEvaluation.controlled source source_mem_FP).reservedPrefix
    parameterCount_unary.computableInPolyTime (fun w => (parameterCount_lt_arity w).le)

noncomputable def controlledGuardedCounterexample : Controlled guardedCounterexample encBits 0 :=
  controlledCounterexample.conditional
    (Controlled.constant controlledCounterexample.arity_computable (fun _ => 0) (.const 0))
    frameFlag frameFlag_polyTime

/-- Every encoded existential-universal real sentence is decided at one fixed
counting level, with no promise on the input word. -/
theorem mem_CountingLevel : language ∈ CountingLevel 60 encBits := by
  have hn := ComputableInPolyTime.unary_sub'
    (TermEvaluation.arity_unary source source_mem_FP).computableInPolyTime
    parameterCount_unary.computableInPolyTime
  have h := controlledGuardedCounterexample.twoBlock_mem Decoder.bits hn
    parameterCount_unary.computableInPolyTime
  convert h using 1
  ext w
  exact guardedCounterexample_avoidance w

/-- The complexity class defined by polynomial-time many-one reductions to the
encoded two-block real language. -/
def RealClass : Set Language := {L | PolyTimeReduces L language}

/-- Every problem reducible to the two-block real theory has the same bound. -/
theorem realClass_subset_CountingLevel : RealClass ⊆ CountingLevel 60 encBits := by
  intro L hL
  exact hL.mem_CountingLevel mem_CountingLevel

end LeanCanny.CountingHierarchy.ExistsForall
