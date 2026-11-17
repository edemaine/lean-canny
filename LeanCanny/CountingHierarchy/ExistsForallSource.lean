/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FiberEquationCompiler
public import LeanCanny.CountingHierarchy.Controlled

/-! # A native counterexample equation with a reserved existential parameterCount -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.ExistsForall

open LeanCanny LeanCanny.Encoding LeanCanny.Encoding.Brackets LeanCanny.ETR
open Cslib Cslib.Complexity Turing.MultiTapeTM

abbrev encSentence : (ℕ × List Bool) ↪ List Bool := encPair encUnary encBits

def decoder : Decoder encSentence := Decoder.pair Decoder.unary Decoder.bits

def parameterCount (w : List Bool) : ℕ := (decoder.decode w).1

def matrixBits (w : List Bool) : List Bool := (decoder.decode w).2

theorem parameterCount_unary : UnaryFn parameterCount := by
  change ComputableTidilyInPolyTime (fun w => parameterCount w) encBits encUnary
  simpa only [parameterCount, Function.comp_def] using
    ((ComputableInPolyTime.fst encUnary encBits).comp decoder.computableInPolyTime).tidy

theorem matrixBits_mem_FP : matrixBits ∈ FP := by
  change ComputableTidilyInPolyTime (fun w => matrixBits w) encBits encBits
  simpa only [matrixBits, Function.comp_def] using
    ((ComputableInPolyTime.snd encUnary encBits).comp decoder.computableInPolyTime).tidy

noncomputable def matrix (w : List Bool) : Formula := Classical.choose (NNF.normalize_shape (matrixBits w))

theorem matrix_encode (w : List Bool) : NNF.normalize (matrixBits w) = (matrix w).encode :=
  (Classical.choose_spec (NNF.normalize_shape (matrixBits w))).1

def dummy (r : ℕ) : Term := .mul (.const 0) (.var r)

noncomputable def counterFormula (w : List Bool) : Formula := .and ((matrix w).nnf false) (.eqZero (dummy (parameterCount w)))

def dummyBits (w : List Bool) : List Bool :=
  Codec.taggedTwo 3 (Term.const 0).toData.toBits (Term.variableBits (parameterCount w))

def counterBits (w : List Bool) : List Bool :=
  Codec.taggedTwo 4 (NNF.transformBits false (NNF.normalize (matrixBits w))) (Codec.taggedOne 1 (dummyBits w))

def source (w : List Bool) : List Bool :=
  Codec.taggedTwo 2 (RationalSubstitutionBits.compiledTerm (counterBits w)) (dummyBits w)

theorem dummyBits_mem_FP : dummyBits ∈ FP :=
  Codec.taggedTwo_mem_FP 3 (constFn_mem_FP _) (Term.variableBits_mem_FP parameterCount_unary)

theorem counterBits_mem_FP : counterBits ∈ FP := by
  change (fun w => counterBits w) ∈ FP
  have hnorm := mem_FP_comp matrixBits_mem_FP NNF.normalize_mem_FP
  have hneg := mem_FP_comp hnorm (NNF.transformBits_mem_FP false)
  simpa only [counterBits, Function.comp_def] using
    Codec.taggedTwo_mem_FP 4 hneg (Codec.taggedOne_mem_FP 1 dummyBits_mem_FP)

theorem source_mem_FP : source ∈ FP := by
  change (fun w => source w) ∈ FP
  simpa only [source, Function.comp_def] using Codec.taggedTwo_mem_FP 2
    (mem_FP_comp counterBits_mem_FP RationalSubstitutionBits.compiledTerm_mem_FP) dummyBits_mem_FP

theorem dummyBits_eq (w : List Bool) : dummyBits w = (dummy (parameterCount w)).toData.toBits := by
  rw [dummyBits, Term.variableBits_eq, ← Term.mul_toBits]
  rfl

theorem and_encode (p q : Formula) : (Formula.and p q).encode = Codec.taggedTwo 4 p.encode q.encode := by
  simp only [Formula.encode, Codec.taggedTwo_toBits, Formula.toData]

theorem negativeMatrixBits_eq (w : List Bool) :
    NNF.transformBits false (NNF.normalize (matrixBits w)) = ((matrix w).nnf false).encode := by
  rw [matrix_encode]
  change NNF.transformBits false (matrix w).toData.toBits = _
  rw [NNF.transformBits_toBits, NNF.dual_formula]
  rfl

theorem counterBits_eq (w : List Bool) : counterBits w = (counterFormula w).encode := by
  rw [counterBits, negativeMatrixBits_eq, dummyBits_eq, ← Formula.eqZero_encode, ← and_encode]
  rfl

noncomputable def sourceTerm (w : List Bool) : Term :=
  .add (TermView.term (RationalSubstitutionBits.compiledTerm (counterBits w))) (dummy (parameterCount w))

theorem source_eq (w : List Bool) : source w = (sourceTerm w).toData.toBits := by
  obtain ⟨t, _, ht⟩ := RationalSubstitutionBits.compiledTerm_shape (counterBits w)
  rw [source, ht, dummyBits_eq, sourceTerm, ht, TermView.term_toBits, Term.add_toBits]

theorem source_term_eq (w : List Bool) : TermView.term (source w) = sourceTerm w := by
  rw [source_eq, TermView.term_toBits]

theorem source_eval (w : List Bool) (env : ℕ → ℝ) :
    (TermView.term (source w)).eval env =
      (TermView.term (RationalSubstitutionBits.compiledTerm (counterBits w))).eval env := by
  rw [source_term_eq]
  simp only [sourceTerm, dummy, Term.eval, Int.cast_zero, zero_mul, add_zero]

theorem parameterCount_lt_arity (w : List Bool) : parameterCount w < TermEvaluation.arity source w := by
  rw [TermEvaluation.arity_eq, source_term_eq]
  have ht := (sourceTerm w).arity_le_dataSize
  have hp : parameterCount w + 1 ≤ (sourceTerm w).arity := by
    simp only [sourceTerm, dummy, Term.arity, Nat.zero_max]
    exact le_max_right _ _
  omega

theorem parameterCount_le_counter_start (w : List Bool) : parameterCount w ≤ ((counterFormula w).nnf true).encode.length := by
  have hvar : parameterCount w + 1 ≤ (counterFormula w).arity := by
    simp only [counterFormula, dummy, Formula.arity, Term.arity, Nat.zero_max]
    exact le_max_right _ _
  have he := ((counterFormula w).nnf true).arity_le_dataSize
  rw [Formula.nnf_arity] at he
  simp only [Formula.encode, Data.length_toBits]
  omega

theorem source_parameterCount_fiber_iff (w : List Bool) (x : Fin (parameterCount w) → ℝ) :
    (∃ env : ℕ → ℝ, (∀ i : Fin (parameterCount w), env i.val = x i) ∧ ¬(matrix w).Holds env) ↔
      ∃ env : ℕ → ℝ, (∀ i : Fin (parameterCount w), env i.val = x i) ∧
        (TermView.term (source w)).eval env = 0 := by
  simp only [source_eval, counterBits_eq]
  have h := compiledTerm_prefix_fiber_iff (counterFormula w) (parameterCount w) (parameterCount_le_counter_start w) x
  simpa only [counterFormula, Formula.Holds, Formula.holds_nnf, Bool.false_eq_true, ↓reduceIte,
    dummy, Term.eval, Int.cast_zero, zero_mul, and_true] using h

end LeanCanny.CountingHierarchy.ExistsForall
