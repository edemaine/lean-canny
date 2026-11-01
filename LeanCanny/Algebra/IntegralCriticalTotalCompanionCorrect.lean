/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalCompanion
public import LeanCanny.Algebra.IntegralCriticalTotalCompanionModel
public import LeanCanny.Algebra.IntegralCriticalTotalCompanionInvariant
/-! # Total companion correctness for actual creating polynomials -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalFlatHeightBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralScalarGeneratorBits.viewValue coefficient leading leadingInteger

theorem model_program_value (F : Scripts) (q : List Bool) (h : valid F q)
    (answer : List Bool → List Bool) :
    (IntegralScalarGeneratorBits.program (family F) (IntegralCriticalFlatCompanionBits.writer F.toParameters)).value answer q =
      (IntegralScalarGeneratorBits.program (model F q h) (fun _ => child F q)).value answer q := by
  rw [IntegralScalarGeneratorBits.program_view, IntegralScalarGeneratorBits.program_view]
  rw [model_row, model_col, model_oldRow, model_oldCol, model_leading, model_scalarDegree, model_selectedDegree]
  rfl

theorem program_value (F : Scripts) (answer : List Bool → List Bool)
    (ha : ∀ q, valid F q → IntegralScalarGeneratorBits.request (family F) q →
      answer (child F q) = residueBits (coefficient F q
        (IntegralScalarGeneratorBits.index (family F) q) (oldRow F q) (oldCol F q)))
    (q : List Bool) : (program F).value answer q = companionValue F q := by
  by_cases h : valid F q
  · rw [valid_value F answer q h, model_program_value F q h answer]
    have HC : ∀ c, IntegralScalarGeneratorBits.request (model F q h) c →
        answer (child F q) = residueBits ((model F q h).coefficient c
          (IntegralScalarGeneratorBits.index (model F q h) c)
          ((model F q h).oldRow c) ((model F q h).oldCol c)) := by
      intro c hc
      rw [model_index, model_coefficient]
      exact ha q h ((model_request F q h c).mp hc)
    have HV := IntegralCriticalScriptGeneratorBits.program_value (queries F q h) (fun _ => child F q) answer HC q
    exact HV.trans (generator_value F (fun _ => q) (fun _ => h) q)
  · rw [missing_value F answer q h]
    unfold companionValue
    rw [dite_eq_right h]
end LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
