/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActualLowerPacket
/-! # Fresh actual lower children preserve every native selector -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualLowerChildBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily

noncomputable def child (F : Scripts) (c : List Bool) : List Bool :=
  IntegralCriticalFlatLowerQuery.writer F.toParameters (input F c)

theorem input_bounds (F : Scripts) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c) :
    Nat.fromBitsLE (basisRowCode (input F c)) ≤ numericCap F.toParameters (RankedHistoryTask.root c) ∧
    Nat.fromBitsLE (basisColCode (input F c)) ≤ numericCap F.toParameters (RankedHistoryTask.root c) ∧
    Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex (input F c)) ≤ numericCap F.toParameters (RankedHistoryTask.root c) ∧
    Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex (input F c)) ≤ numericCap F.toParameters (RankedHistoryTask.root c) := by
  have HR : (relative F).rank c ≤ numericCap F.toParameters (RankedHistoryTask.root c) :=
    IntegralCriticalActualCaps.rank_cap F c hv
  have HP : 0 < (relative F).rank c := (Nat.zero_le ((relative F).basisRow c).val).trans_lt ((relative F).basisRow c).isLt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [input_row]
    exact (Nat.mod_lt _ HP).le.trans HR
  · rw [input_col]
    exact (Nat.mod_lt _ HP).le.trans HR
  · have HF := IntegralCriticalActualCaps.free_le F c hv
    exact (input_derivative_le F c).trans (HF.trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.1)
  · exact (input_target_lt F c).le.trans (IntegralCriticalActualCaps.target_grid_cap F c hv)

theorem child_root (F : Scripts) (c : List Bool) : RankedHistoryTask.root (child F c) = RankedHistoryTask.root c :=
  (IntegralCriticalFlatLowerQuery.writer_root _ _).trans (congrArg RankedHistoryTask.root (input_parent F c))

theorem child_birth (F : Scripts) (c : List Bool) : birth F.toParameters (child F c) = birth F.toParameters c :=
  (IntegralCriticalFlatLowerQuery.writer_birth _ _).trans (congrArg (birth F.toParameters) (input_parent F c))

theorem child_modulus (F : Scripts) (c : List Bool) :
    IntegralCriticalHistoryTask.modulus F.toParameters (child F c) = IntegralCriticalHistoryTask.modulus F.toParameters c :=
  (IntegralCriticalFlatLowerQuery.writer_modulus _ _).trans
    (congrArg (IntegralCriticalHistoryTask.modulus F.toParameters) (input_parent F c))

theorem child_fields (F : Scripts) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c) :
    get F.toParameters .derivative (child F c) = Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex (input F c)) ∧
    get F.toParameters .target (child F c) = Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex (input F c)) ∧
    get F.toParameters .row (child F c) = Nat.fromBitsLE (basisRowCode (input F c)) ∧
    get F.toParameters .col (child F c) = Nat.fromBitsLE (basisColCode (input F c)) := by
  have HB := input_bounds F c hv
  simp only [child, IntegralCriticalFlatLowerQuery.writer_get, input_parent, reduceCtorEq, ite_true, ite_false]
  exact ⟨min_eq_left HB.2.2.1, min_eq_left HB.2.2.2, min_eq_left HB.1, min_eq_left HB.2.1⟩

theorem child_value (F : Scripts) (h : Controls F) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c) :
    IntegralCriticalActualScalarModels.lower F (child F c) = (relativeAccess F h).low (input F c) := by
  have HF := child_fields F c hv
  have H := IntegralCriticalActualLowerEntry.lower_transport F (child F c) c
    (Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex (input F c)))
    (Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex (input F c)))
    (Nat.fromBitsLE (basisRowCode (input F c))) (Nat.fromBitsLE (basisColCode (input F c)))
    (child_root F c) (child_birth F c) (child_modulus F c) HF.1 HF.2.1 HF.2.2.1 HF.2.2.2
  exact H.trans (by simpa only [input_parent] using (low_snapshot F h (input F c)).symm)

theorem child_valid (F : Scripts) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c) :
    IntegralCriticalTotalCompanionBits.valid F (child F c) := by
  change birth F.toParameters (child F c) < (F.rules (RankedHistoryTask.root (child F c))).length
  rw [child_birth, child_root]
  exact hv

theorem child_phase (F : Scripts) (c : List Bool) : isPhase .eulerLower (child F c) :=
  IntegralCriticalFlatLowerQuery.writer_phase _ _

theorem child_rank (F : Scripts) (c : List Bool) (hp : isPhase .reductionEntry c) :
    rank F.toParameters (child F c) < rank F.toParameters c := by
  have H := IntegralCriticalFlatLowerQuery.writer_lower_rank F.toParameters (input F c)
  rw [input_parent] at H
  apply H
  change phase c = 17 at hp
  omega

theorem program_value_finite (F : Scripts) (h : Controls F) (answer : List Bool → List Bool) (c : List Bool)
    (hv : IntegralCriticalTotalCompanionBits.valid F c)
    (he : PurePowerReductionBits.request (IntegralPurePowerReductionBits.layout (relative F))
      (fun z => (relative F).layout.bound (pairFst z)) (native F c) →
      answer (child F c) = IntegralCriticalActualScalarModels.lower F (child F c))
    (i j : Fin ((reduction F).dimension c * (reduction F).rank c))
    (hi : get F.toParameters .row c = i.val) (hj : get F.toParameters .col c = j.val) :
    (IntegralCriticalFlatReductionEntryBits.program F.toParameters (relative F) (relativeAccess F h)).value answer c =
      IntegralCriticalFlatActualReductionEntryBits.value F c :=
  IntegralCriticalFlatActualReductionEntryBits.program_value_finite F h answer c
    (fun hg => (he hg).trans (child_value F h c hv)) i j hi hj

end LeanCanny.Algebra.IntegralCriticalFlatActualLowerChildBits
