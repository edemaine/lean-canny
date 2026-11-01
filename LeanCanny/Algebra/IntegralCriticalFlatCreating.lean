/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatHeight
public import LeanCanny.Algebra.IntegralCriticalScriptGenerator

/-! # Actual creating queries on a valid flat-task domain

The full decoder is total and returns zero outside actual script births.
On any valid input domain this constructor supplies the existing actual
ScriptGenerator Queries, with no nonempty-script assumption elsewhere.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial UniformIntegralPrefix
open IntegralCriticalScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def creatingIndex (F : Scripts) (q : List Bool)
    (h : IntegralCriticalHistoryTask.birth F.toParameters q < (F.rules (root q)).length) : Fin (F.rules (root q)).length :=
  ⟨(F.rules (root q)).length - 1 - IntegralCriticalHistoryTask.birth F.toParameters q, by omega⟩

noncomputable def generatorQueries (F : Scripts) (query : List Bool → List Bool)
    (h : ∀ c, IntegralCriticalHistoryTask.birth F.toParameters (query c) < (F.rules (root (query c))).length) :
    IntegralCriticalScriptGeneratorBits.Queries where
  cap c := F.cap (root (query c))
  width c := F.width (root (query c))
  ambient c := F.ambient (root (query c))
  sourceWidth c := F.sourceWidth (root (query c))
  degreeBound c := F.degree (root (query c))
  height c := F.height (root (query c))
  rules c := F.rules (root (query c))
  length_le c := F.length_le (root (query c))
  scalar_bound c := F.scalar_bound (root (query c))
  selected c := creatingIndex F (query c) (h c)
  modulus c := IntegralCriticalHistoryTask.modulus F.toParameters (query c)
  modulus_ne_zero _ := IntegralCriticalHistoryTask.modulus_ne_zero _ _
  row c := ⟨IntegralCriticalHistoryTask.get F.toParameters .row (query c) %
    count ((older (F.rules (root (query c))) (creatingIndex F (query c) (h c))).length + 1) (F.width (root (query c))),
    Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
  col c := ⟨IntegralCriticalHistoryTask.get F.toParameters .col (query c) %
    count ((older (F.rules (root (query c))) (creatingIndex F (query c) (h c))).length + 1) (F.width (root (query c))),
    Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩

theorem generator_birthSource (F : Scripts) (query : List Bool → List Bool)
    (h : ∀ c, IntegralCriticalHistoryTask.birth F.toParameters (query c) < (F.rules (root (query c))).length) (c : List Bool) :
    IntegralCriticalScriptGeneratorBits.birthSource (generatorQueries F query h) c = creatingFamily F (query c) (h c) := rfl

theorem generator_arity (F : Scripts) (query : List Bool → List Bool)
    (h : ∀ c, IntegralCriticalHistoryTask.birth F.toParameters (query c) < (F.rules (root (query c))).length) (c : List Bool) :
    (IntegralCriticalScriptGeneratorBits.generatorFamily (generatorQueries F query h)).arity c =
      IntegralCriticalHistoryTask.birth F.toParameters (query c) := by
  change (older (F.rules (root (query c))) (creatingIndex F (query c) (h c))).length = _
  rw [older_length]
  simp only [creatingIndex]
  have H := h c
  omega

theorem generator_value (F : Scripts) (query : List Bool → List Bool)
    (h : ∀ c, IntegralCriticalHistoryTask.birth F.toParameters (query c) < (F.rules (root (query c))).length) (c : List Bool) :
    (IntegralCriticalScriptGeneratorBits.generatorFamily (generatorQueries F query h)).value c = companionValue F (query c) := by
  have H := IntegralCriticalCreatingBits.birth_value (F.rules (root (query c))) (F.length_le (root (query c)))
    (F.scalar_bound (root (query c))) (creatingIndex F (query c) (h c))
    ((generatorQueries F query h).row c) ((generatorQueries F query h).col c)
    (IntegralCriticalHistoryTask.modulus F.toParameters (query c))
  have HE : IntegralCriticalCreatingBits.value
      (birthFamily (F.rules (root (query c))) (F.length_le (root (query c))) (F.scalar_bound (root (query c)))
        (creatingIndex F (query c) (h c)))
      ((generatorQueries F query h).row c).val ((generatorQueries F query h).col c).val
      (IntegralCriticalHistoryTask.modulus F.toParameters (query c)) = companionValue F (query c) := by
    unfold companionValue
    rw [dite_eq_left (h c)]
    exact IntegralCriticalCreatingBits.value_mod _ _ _ _
  exact (IntegralCriticalScriptGeneratorBits.value (generatorQueries F query h) c).trans (H.symm.trans HE)

end LeanCanny.Algebra.IntegralCriticalFlatHeightBits
