/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalTotalCompanionAccess
public import LeanCanny.Algebra.IntegralScalarGeneratorView

/-! # Valid-task comparison with the actual creating companion source -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalScript IntegralCriticalFlatHeightBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def queries (F : Scripts) (q : List Bool) (h : valid F q) : IntegralCriticalScriptGeneratorBits.Queries :=
  generatorQueries F (fun _ => q) (fun _ => h)

noncomputable def model (F : Scripts) (q : List Bool) (h : valid F q) : IntegralScalarGeneratorBits.Family :=
  IntegralCriticalScriptGeneratorBits.scalarFamily (queries F q h)

theorem model_modulus (F : Scripts) (q : List Bool) (h : valid F q) (c : List Bool) :
    (model F q h).modulus c = IntegralCriticalHistoryTask.modulus F.toParameters q := rfl

theorem model_scalarDegree (F : Scripts) (q : List Bool) (h : valid F q) (c : List Bool) :
    (model F q h).scalarDegree c = scalarDegree F q := rfl

theorem model_selectedDegree (F : Scripts) (q : List Bool) (h : valid F q) (c : List Bool) :
    (model F q h).selectedDegree c = selectedDegree F q := by
  change IntegralScalarRootHistoryBounds.degree (IntegralCriticalScriptGeneratorBits.birthSource (queries F q h) c) [] = _
  rw [show IntegralCriticalScriptGeneratorBits.birthSource (queries F q h) c = creatingFamily F q h from
    generator_birthSource F (fun _ => q) (fun _ => h) c]
  exact (selectedDegree_creating F q h).symm

theorem queries_row (F : Scripts) (q : List Bool) (h : valid F q) (c : List Bool) :
    ((queries F q h).row c).val = row F q := by
  change IntegralCriticalHistoryTask.get F.toParameters .row q %
    count ((older (F.rules (root q)) (creatingIndex F q h)).length + 1) (F.width (root q)) = _
  rw [creating_older_length]
  rfl

theorem queries_col (F : Scripts) (q : List Bool) (h : valid F q) (c : List Bool) :
    ((queries F q h).col c).val = col F q := by
  change IntegralCriticalHistoryTask.get F.toParameters .col q %
    count ((older (F.rules (root q)) (creatingIndex F q h)).length + 1) (F.width (root q)) = _
  rw [creating_older_length]
  rfl

theorem model_row (F : Scripts) (q : List Bool) (h : valid F q) (c : List Bool) :
    ((model F q h).row c).val = (scalarRow F q).val := by
  change ((queries F q h).row c).val % (2 ^ F.width (root q)) = _
  rw [queries_row]
  rfl

theorem model_col (F : Scripts) (q : List Bool) (h : valid F q) (c : List Bool) :
    ((model F q h).col c).val = (scalarCol F q).val := by
  change ((queries F q h).col c).val % (2 ^ F.width (root q)) = _
  rw [queries_col]
  rfl

theorem model_oldRow (F : Scripts) (q : List Bool) (h : valid F q) (c : List Bool) :
    ((model F q h).oldRow c).val = (oldRow F q).val := by
  change ((queries F q h).row c).val / (2 ^ F.width (root q)) = _
  rw [queries_row]
  rfl

theorem model_oldCol (F : Scripts) (q : List Bool) (h : valid F q) (c : List Bool) :
    ((model F q h).oldCol c).val = (oldCol F q).val := by
  change ((queries F q h).col c).val / (2 ^ F.width (root q)) = _
  rw [queries_col]
  rfl

theorem model_leading (F : Scripts) (q : List Bool) (h : valid F q) (c : List Bool) :
    (model F q h).leading c = leading F q := by
  unfold leading leadingInteger
  rw [dite_eq_left h]
  change (IntegralHistoryCriticalBits.leadingInteger
    (IntegralCriticalScriptGeneratorBits.birthSource (queries F q h) c) :
      ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q)) = _
  rw [show IntegralCriticalScriptGeneratorBits.birthSource (queries F q h) c = creatingFamily F q h from
    generator_birthSource F (fun _ => q) (fun _ => h) c]

theorem model_request (F : Scripts) (q : List Bool) (h : valid F q) (c : List Bool) :
    IntegralScalarGeneratorBits.request (model F q h) c ↔ IntegralScalarGeneratorBits.request (family F) q := by
  unfold IntegralScalarGeneratorBits.request
  rw [model_col, model_row, model_scalarDegree, model_selectedDegree]
  rfl

theorem model_index (F : Scripts) (q : List Bool) (h : valid F q) (c : List Bool) :
    IntegralScalarGeneratorBits.index (model F q h) c = IntegralScalarGeneratorBits.index (family F) q := by
  unfold IntegralScalarGeneratorBits.index
  rw [model_row, model_scalarDegree, model_selectedDegree]
  rfl

theorem model_coefficient (F : Scripts) (q : List Bool) (h : valid F q) (c : List Bool) (k : ℕ) :
    (model F q h).coefficient c k ((model F q h).oldRow c) ((model F q h).oldCol c) =
      coefficient F q k (oldRow F q) (oldCol F q) := by
  rw [coefficient_creating F q h]
  rw [← model_oldRow F q h c, ← model_oldCol F q h c]
  have H : IntegralCriticalScriptGeneratorBits.birthSource (queries F q h) c = creatingFamily F q h :=
    generator_birthSource F (fun _ => q) (fun _ => h) c
  rw [← H]
  exact (IntegralCriticalScriptGeneratorBits.coefficientEntry_eq (queries F q h) c k
    ((model F q h).oldRow c) ((model F q h).oldCol c)).symm

end LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
