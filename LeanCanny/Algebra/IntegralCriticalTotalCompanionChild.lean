/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalCompanionCorrect
public import LeanCanny.Algebra.IntegralCriticalTotalCoefficientValue
/-! # Exact same-birth coefficient child of a total companion task -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] coefficient leading leadingInteger

theorem oldRank_le (F : Scripts) (q : List Bool) : oldRank F q ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (root q) :=
  IntegralCriticalHistoryTask.born_rank_le _ _ (min_le_right _ _)

theorem scalarDegree_le (F : Scripts) (q : List Bool) : scalarDegree F q ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (root q) :=
  (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.2.2.2.1

theorem child_fields (F : Scripts) (q : List Bool) :
    IntegralCriticalHistoryTask.get F.toParameters .row (child F q) = (oldRow F q).val ∧
    IntegralCriticalHistoryTask.get F.toParameters .col (child F q) = (oldCol F q).val ∧
    IntegralCriticalHistoryTask.get F.toParameters .coefficient (child F q) = IntegralScalarGeneratorBits.index (family F) q := by
  apply IntegralCriticalFlatCompanionBits.writer_packet_fields
  · exact (oldRow F q).isLt.le.trans (oldRank_le F q)
  · exact (oldCol F q).isLt.le.trans (oldRank_le F q)
  · exact (Nat.sub_le _ _).trans ((scalarRow F q).isLt.le.trans (scalarDegree_le F q))

theorem child_modulus (F : Scripts) (q : List Bool) :
    IntegralCriticalHistoryTask.modulus F.toParameters (child F q) = IntegralCriticalHistoryTask.modulus F.toParameters q := by
  unfold child
  rw [IntegralCriticalFlatCompanionBits.writer_modulus]
  simp only [IntegralScalarGeneratorBits.coefficientQuery, pairFst_pair]

theorem child_valid (F : Scripts) (q : List Bool) : valid F (child F q) ↔ valid F q := by
  change IntegralCriticalHistoryTask.birth F.toParameters (child F q) < (F.rules (root (child F q))).length ↔ _
  rw [child_birth, child_root]

theorem child_coefficient_value (F : Scripts) (q : List Bool) (h : valid F q) :
    coefficientValue F (child F q) = residueBits (coefficient F q
      (IntegralScalarGeneratorBits.index (family F) q) (oldRow F q) (oldCol F q)) := by
  unfold coefficientValue
  rw [(child_fields F q).1, (child_fields F q).2.1, (child_fields F q).2.2]
  rw [coefficientAt_invariance F (child F q) q ((child_valid F q).mpr h) h
    (child_root F q) (child_birth F q) (child_modulus F q)]
  unfold coefficientAt
  simp only [Nat.mod_eq_of_lt (oldRow F q).isLt, Nat.mod_eq_of_lt (oldCol F q).isLt]

theorem program_coefficientValue (F : Scripts) (answer : List Bool → List Bool)
    (ha : ∀ q, valid F q → IntegralScalarGeneratorBits.request (family F) q →
      answer (child F q) = coefficientValue F (child F q)) (q : List Bool) :
    (program F).value answer q = IntegralCriticalFlatHeightBits.companionValue F q := by
  apply program_value F answer
  intro c hc hr
  exact (ha c hc hr).trans (child_coefficient_value F c hc)
end LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
