/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.Grammar
public import LeanCanny.ETR.EquationSize

/-! # A total validated expression view for encoded source routines -/

@[expose] public section

namespace LeanCanny.ETR.TermView
open Complexity

def normalize (bits : List Bool) : List Bool :=
  if Grammar.recognizeTerm bits then bits else (Term.const 0).toData.toBits

noncomputable def term (bits : List Bool) : Term :=
  if h : Grammar.recognizeTerm bits = true then Classical.choose ((Grammar.recognizeTerm_true_iff bits).mp h)
  else .const 0

theorem normalize_mem_FP : normalize ∈ FP :=
  (FPPred.of_flag Grammar.recognizeTerm_mem_FP).ite_mem_FP id_mem_FP (constFn_mem_FP (Term.const 0).toData.toBits)

theorem normalize_eq_term (bits : List Bool) : normalize bits = (term bits).toData.toBits := by
  unfold normalize term
  split_ifs with h
  · exact Classical.choose_spec ((Grammar.recognizeTerm_true_iff bits).mp h)
  · rfl

theorem normalize_toBits (t : Term) : normalize t.toData.toBits = t.toData.toBits := by
  simp only [normalize, Grammar.recognizeTerm_toBits, ↓reduceIte]

theorem term_toBits (t : Term) : term t.toData.toBits = t := by
  apply Term.toData_injective
  apply Data.toBits_injective
  rw [← normalize_eq_term, normalize_toBits]

theorem normalize_length_le (bits : List Bool) : (normalize bits).length ≤ bits.length + 10 := by
  unfold normalize
  split_ifs
  · omega
  · simp only [Data.length_toBits, Term.dataSize_const_zero]; omega

end LeanCanny.ETR.TermView
