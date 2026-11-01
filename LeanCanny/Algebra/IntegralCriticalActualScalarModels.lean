/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalFrozenStages
public import LeanCanny.Algebra.IntegralCriticalTotalCreatingSnapshot
public import LeanCanny.Algebra.IntegralCriticalFlatGenericEuler
/-! # Canonical scalar models of the actual flat Euler and frozen stages

All algebra and polynomial data comes from the exact creating-family
snapshot. Only natural output selectors remain outside that snapshot.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualScalarModels
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily

noncomputable def eulerAt (A : IntegralHistoryCriticalBits.Family) := (IntegralHistoryCriticalBits.source A).toEuler
noncomputable def selectedAt (A : IntegralHistoryCriticalBits.Family) (j : ℕ) (c : List Bool) : Fin ((eulerAt A).free c) :=
  ⟨j % (eulerAt A).free c, Nat.mod_lt _ ((eulerAt A).free_pos c)⟩
noncomputable def lowerAt (A : IntegralHistoryCriticalBits.Family) (j : ℕ) := (eulerAt A).lowerValue (selectedAt A j) []
noncomputable def objectiveAt (A : IntegralHistoryCriticalBits.Family) := (eulerAt A).objectiveValue []
noncomputable def sumAt (A : IntegralHistoryCriticalBits.Family) := (eulerAt A).sumValue []
noncomputable def frozenLowerAt (A : IntegralHistoryCriticalBits.Family) := (eulerAt A).toGradient.toFrozen.lowerValue []
noncomputable def frozenConstantAt (A : IntegralHistoryCriticalBits.Family) := (eulerAt A).toGradient.toFrozen.constantValue []
noncomputable def frozenSumAt (A : IntegralHistoryCriticalBits.Family) := (eulerAt A).toGradient.toFrozen.sumValue []
noncomputable def frozenTermAt (A : IntegralHistoryCriticalBits.Family) (i : ℕ) :=
  IntegralFrozenPowerBits.termProgram (eulerAt A).toGradient.toFrozen (pair [] (BinaryNatCode.encode i))

noncomputable def lower (F : Scripts) (q : List Bool) :=
  lowerAt (IntegralCriticalTotalSnapshotBits.family F q) (IntegralCriticalHistoryTask.get F.toParameters .derivative q)
noncomputable def objective (F : Scripts) (q : List Bool) := objectiveAt (IntegralCriticalTotalSnapshotBits.family F q)
noncomputable def sum (F : Scripts) (q : List Bool) := sumAt (IntegralCriticalTotalSnapshotBits.family F q)
noncomputable def frozenLower (F : Scripts) (q : List Bool) := frozenLowerAt (IntegralCriticalTotalSnapshotBits.family F q)
noncomputable def frozenConstant (F : Scripts) (q : List Bool) := frozenConstantAt (IntegralCriticalTotalSnapshotBits.family F q)
noncomputable def frozenSum (F : Scripts) (q : List Bool) := frozenSumAt (IntegralCriticalTotalSnapshotBits.family F q)
noncomputable def frozenTerm (F : Scripts) (q : List Bool) :=
  frozenTermAt (IntegralCriticalTotalSnapshotBits.family F q) (IntegralCriticalHistoryTask.get F.toParameters .slot8 q)

theorem lower_eq (F : Scripts) (q : List Bool) : lower F q =
    (IntegralCriticalTotalCreatingBits.euler F).lowerValue
      (IntegralCriticalFlatEulerRowsBits.selected F.toParameters (IntegralCriticalTotalCreatingBits.euler F)) q := rfl
theorem objective_eq (F : Scripts) (q : List Bool) : objective F q = (IntegralCriticalTotalCreatingBits.euler F).objectiveValue q := rfl
theorem sum_eq (F : Scripts) (q : List Bool) : sum F q = (IntegralCriticalTotalCreatingBits.euler F).sumValue q := rfl
theorem frozenLower_eq (F : Scripts) (q : List Bool) : frozenLower F q = (IntegralCriticalTotalCreatingBits.euler F).toGradient.toFrozen.lowerValue q := rfl
theorem frozenConstant_eq (F : Scripts) (q : List Bool) : frozenConstant F q = (IntegralCriticalTotalCreatingBits.euler F).toGradient.toFrozen.constantValue q := rfl
theorem frozenSum_eq (F : Scripts) (q : List Bool) : frozenSum F q = (IntegralCriticalTotalCreatingBits.euler F).toGradient.toFrozen.sumValue q := rfl
theorem frozenTerm_packet_eq (F : Scripts) (q : List Bool) (i : ℕ) :
    frozenTermAt (IntegralCriticalTotalSnapshotBits.family F q) i =
      IntegralFrozenPowerBits.termProgram (IntegralCriticalTotalCreatingBits.euler F).toGradient.toFrozen
        (pair q (BinaryNatCode.encode i)) := by
  unfold frozenTermAt
  rw [IntegralFrozenPowerBits.term_packet, IntegralFrozenPowerBits.term_packet]
  rfl
theorem frozenTerm_eq (F : Scripts) (q : List Bool) : frozenTerm F q =
    IntegralFrozenPowerBits.termProgram (IntegralCriticalTotalCreatingBits.euler F).toGradient.toFrozen
      (IntegralCriticalFlatFrozenTermBits.input F.toParameters q) := frozenTerm_packet_eq F q _

theorem objective_next (F : Scripts) (p : IntegralCriticalHistoryTask.Phase) (q : List Bool) :
    objective F (IntegralCriticalFlatEulerBits.next F.toParameters p q) = objective F q :=
  congrArg objectiveAt (IntegralCriticalTotalSnapshotBits.family_next F p q)
theorem sum_next (F : Scripts) (p : IntegralCriticalHistoryTask.Phase) (q : List Bool) :
    sum F (IntegralCriticalFlatEulerBits.next F.toParameters p q) = sum F q :=
  congrArg sumAt (IntegralCriticalTotalSnapshotBits.family_next F p q)
theorem frozenLower_next (F : Scripts) (p : IntegralCriticalHistoryTask.Phase) (q : List Bool) :
    frozenLower F (IntegralCriticalFlatEulerBits.next F.toParameters p q) = frozenLower F q :=
  congrArg frozenLowerAt (IntegralCriticalTotalSnapshotBits.family_next F p q)
theorem frozenConstant_next (F : Scripts) (p : IntegralCriticalHistoryTask.Phase) (q : List Bool) :
    frozenConstant F (IntegralCriticalFlatEulerBits.next F.toParameters p q) = frozenConstant F q :=
  congrArg frozenConstantAt (IntegralCriticalTotalSnapshotBits.family_next F p q)
theorem frozenSum_next (F : Scripts) (p : IntegralCriticalHistoryTask.Phase) (q : List Bool) :
    frozenSum F (IntegralCriticalFlatEulerBits.next F.toParameters p q) = frozenSum F q :=
  congrArg frozenSumAt (IntegralCriticalTotalSnapshotBits.family_next F p q)
theorem lower_next (F : Scripts) (p : IntegralCriticalHistoryTask.Phase) (q : List Bool) :
    lower F (IntegralCriticalFlatEulerBits.next F.toParameters p q) = lower F q := by
  unfold lower
  rw [IntegralCriticalTotalSnapshotBits.family_next, IntegralCriticalFlatEulerBits.next_get]

theorem family_coordinate (F : Scripts) (p : IntegralCriticalHistoryTask.Phase) (q : List Bool) (i : ℕ) :
    IntegralCriticalTotalSnapshotBits.family F
      (IntegralCriticalFlatCoordinateQuery.writer F.toParameters p (pair q (BinaryNatCode.encode i))) =
      IntegralCriticalTotalSnapshotBits.family F q := by
  apply IntegralCriticalTotalSnapshotBits.family_invariance
  · simpa only [root, IntegralCriticalFlatHeightBits.root, pairFst_pair] using
      IntegralCriticalFlatCoordinateQuery.writer_root F.toParameters p (pair q (BinaryNatCode.encode i))
  · simpa only [pairFst_pair] using IntegralCriticalFlatCoordinateQuery.writer_birth F.toParameters p (pair q (BinaryNatCode.encode i))
  · simpa only [pairFst_pair] using IntegralCriticalFlatCoordinateQuery.writer_modulus F.toParameters p (pair q (BinaryNatCode.encode i))
  all_goals
    simpa only [pairFst_pair] using IntegralCriticalFlatCoordinateQuery.writer_other F.toParameters p
      (pair q (BinaryNatCode.encode i)) _ (by decide)

theorem frozenSum_child (F : Scripts) (q : List Bool) (i : ℕ)
    (hi : i ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q)) :
    frozenTerm F (IntegralCriticalFlatCoordinateQuery.writer F.toParameters .frozenPowerTerm (pair q (BinaryNatCode.encode i))) =
      IntegralFrozenPowerBits.termProgram (IntegralCriticalTotalCreatingBits.euler F).toGradient.toFrozen
        (pair q (BinaryNatCode.encode i)) := by
  unfold frozenTerm
  rw [family_coordinate, IntegralCriticalFlatCoordinateQuery.writer_coordinate _ _ _ _ hi]
  exact frozenTerm_packet_eq F q i

theorem arity_cap (F : Scripts) (q : List Bool) :
    (IntegralCriticalTotalCreatingBits.euler F).arity q ≤
      IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q) := by
  change (IntegralCriticalTotalCreatingBits.atFamily F q).ambient [] + 1 ≤ _
  rw [IntegralCriticalTotalCreatingBits.at_ambient]
  split_ifs
  · exact (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.1
  · exact Nat.succ_le_of_lt (IntegralCriticalHistoryTask.numericCap_pos _ _)

theorem frozenSum_child_finite (F : Scripts) (q : List Bool) (i : ℕ)
    (hi : i < (IntegralCriticalTotalCreatingBits.euler F).arity q) :
    frozenTerm F (IntegralCriticalFlatCoordinateQuery.writer F.toParameters .frozenPowerTerm (pair q (BinaryNatCode.encode i))) =
      IntegralFrozenPowerBits.termProgram (IntegralCriticalTotalCreatingBits.euler F).toGradient.toFrozen
        (pair q (BinaryNatCode.encode i)) := frozenSum_child F q i (hi.le.trans (arity_cap F q))

theorem lower_objective_child (F : Scripts) (q : List Bool) :
    objective F (IntegralCriticalFlatEulerBits.next F.toParameters .eulerObjective q) =
      (IntegralCriticalTotalCreatingBits.euler F).objectiveValue q :=
  (objective_next F _ q).trans (objective_eq F q)
theorem objective_lower_child (F : Scripts) (q : List Bool) :
    frozenLower F (IntegralCriticalFlatEulerBits.next F.toParameters .frozenLower q) =
      (IntegralCriticalTotalCreatingBits.euler F).toGradient.toFrozen.lowerValue q :=
  (frozenLower_next F _ q).trans (frozenLower_eq F q)
theorem objective_sum_child (F : Scripts) (q : List Bool) :
    sum F (IntegralCriticalFlatEulerBits.next F.toParameters .eulerSum q) =
      (IntegralCriticalTotalCreatingBits.euler F).sumValue q :=
  (sum_next F _ q).trans (sum_eq F q)
theorem frozenLower_constant_child (F : Scripts) (q : List Bool) :
    frozenConstant F (IntegralCriticalFlatEulerBits.next F.toParameters .frozenConstant q) =
      (IntegralCriticalTotalCreatingBits.euler F).toGradient.toFrozen.constantValue q :=
  (frozenConstant_next F _ q).trans (frozenConstant_eq F q)
theorem frozenConstant_sum_child (F : Scripts) (q : List Bool) :
    frozenSum F (IntegralCriticalFlatEulerBits.next F.toParameters .frozenPowerSum q) =
      (IntegralCriticalTotalCreatingBits.euler F).toGradient.toFrozen.sumValue q :=
  (frozenSum_next F _ q).trans (frozenSum_eq F q)

end LeanCanny.Algebra.IntegralCriticalActualScalarModels
