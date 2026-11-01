/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActualMomentTypedRoutes
public import LeanCanny.Algebra.MatrixMomentEntryTypedReplies
/-! # Every selected phase-twenty-one child has its actual action value -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualMomentRoutes
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralBerkowitzBlockBits IntegralCriticalFlatActualMomentBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] characteristic characteristicAccess IntegralCriticalTotalCreatingBits.atFamily

theorem replies (F : Scripts) (h : Controls F) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c) :
    IntegralCriticalFlatMomentEntryBits.RepliesAt F.toParameters h.task.toAccess (characteristic F)
      (characteristicAccess F h) (actionValue F) c := by
  let r : Fin (IntegralCriticalTotalMomentSnapshotBits.size F c) :=
    ⟨get F.toParameters .row c % IntegralCriticalTotalMomentSnapshotBits.size F c, Nat.mod_lt _ (size_pos F c)⟩
  let t : Fin (IntegralCriticalTotalMomentSnapshotBits.size F c) :=
    ⟨get F.toParameters .col c % IntegralCriticalTotalMomentSnapshotBits.size F c, Nat.mod_lt _ (size_pos F c)⟩
  have HI : IntegralCriticalFlatMomentEntryBits.input F.toParameters (characteristic F) c =
      pair (IntegralBlockMomentBits.context c r.modNat.val t.modNat.val)
        (pair (BinaryNatCode.encode r.divNat.val) (BinaryNatCode.encode t.divNat.val)) :=
    IntegralBlockMomentBits.outer_packet (moment F) c r t
  have HD : (IntegralCriticalFlatMomentEntryBits.bits F.toParameters h.task.toAccess (characteristic F)
      (characteristicAccess F h)).dimension (IntegralBlockMomentBits.context c r.modNat.val t.modNat.val) =
      BinaryNatCode.encode ((moment F).dimension c) := by
    simp only [IntegralCriticalFlatMomentEntryBits.bits, IntegralBlockMomentBits.bitsAccess,
      IntegralBlockMomentBits.context, pairFst_pair]
  exact MatrixMoment.EntryBits.repliesAt_of_typed _ _ _ _ _ _ c
    (IntegralBlockMomentBits.context c r.modNat.val t.modNat.val) ((moment F).dimension c) r.divNat t.divNat HD HI
    (fun i => rowTask_value F h c hv i r.modNat t.modNat)
    (fun i => columnTask_value F h c hv i r.modNat t.modNat)
    (fun i j => matrixTask_value F h c hv i j r.modNat t.modNat)

theorem program_value (F : Scripts) (h : Controls F) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c) :
    (IntegralCriticalFlatMomentEntryBits.program F.toParameters h.task.toAccess (characteristic F)
      (characteristicAccess F h)).value (actionValue F) c = IntegralCriticalFlatActualMomentBits.value F c :=
  IntegralCriticalFlatActualMomentBits.program_value F h _ c (replies F h c hv)

theorem program_value_local (F : Scripts) (h : Controls F) (answer : List Bool → List Bool)
    (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c)
    (ha : (IntegralCriticalFlatMomentEntryBits.program F.toParameters h.task.toAccess (characteristic F)
      (characteristicAccess F h)).request c = true →
      answer ((IntegralCriticalFlatMomentEntryBits.program F.toParameters h.task.toAccess (characteristic F)
        (characteristicAccess F h)).query c) =
      actionValue F ((IntegralCriticalFlatMomentEntryBits.program F.toParameters h.task.toAccess (characteristic F)
        (characteristicAccess F h)).query c)) :
    (IntegralCriticalFlatMomentEntryBits.program F.toParameters h.task.toAccess (characteristic F)
      (characteristicAccess F h)).value answer c = IntegralCriticalFlatActualMomentBits.value F c := by
  have HE : (IntegralCriticalFlatMomentEntryBits.program F.toParameters h.task.toAccess (characteristic F)
      (characteristicAccess F h)).value answer c =
      (IntegralCriticalFlatMomentEntryBits.program F.toParameters h.task.toAccess (characteristic F)
        (characteristicAccess F h)).value (actionValue F) c := by
    unfold SingleCall.Program.value
    split_ifs with hr
    · rw [ha hr]
    · rfl
  exact HE.trans (program_value F h c hv)

end LeanCanny.Algebra.IntegralCriticalFlatActualMomentRoutes
