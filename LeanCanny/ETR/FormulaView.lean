/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.Grammar

/-! # A total validated formula view

Malformed words denote falsum. The encoded view is computed by the native
polynomial-time grammar recognizer and preserves every valid formula exactly.
-/

@[expose] public section

namespace LeanCanny.ETR.FormulaView

def normalize (bits : List Bool) : List Bool :=
  if Grammar.recognizeFormula bits then bits else Formula.falsum.encode

noncomputable def formula (bits : List Bool) : Formula :=
  if h : Grammar.recognizeFormula bits = true then
    Classical.choose ((Grammar.recognizeFormula_true_iff bits).mp h) else .falsum

theorem normalize_mem_FP : normalize ∈ FP :=
  (FPPred.of_flag Grammar.recognizeFormula_mem_FP).ite_mem_FP id_mem_FP
    (constFn_mem_FP Formula.falsum.encode)

theorem normalize_eq_formula (bits : List Bool) : normalize bits = (formula bits).encode := by
  unfold normalize formula
  split_ifs with h
  · exact Classical.choose_spec ((Grammar.recognizeFormula_true_iff bits).mp h)
  · rfl

@[simp] theorem normalize_encode (p : Formula) : normalize p.encode = p.encode := by
  simp [normalize, Grammar.recognizeFormula_encode]

@[simp] theorem formula_encode (p : Formula) : formula p.encode = p := by
  apply Formula.encode_injective
  rw [← normalize_eq_formula, normalize_encode]

theorem encoded_computable : Turing.MultiTapeTM.ComputableTidilyInPolyTime
    (fun bits => (formula bits).encode) Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits :=
  normalize_mem_FP.of_enc_eq fun bits => (normalize_eq_formula bits).symm

end LeanCanny.ETR.FormulaView
