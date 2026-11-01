/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationSnapshots
/-! # Fresh phase-four trailing-moment requests for normalization -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false

theorem saved_next (P : Parameters) (p : Phase) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (IntegralCriticalFlatEulerBits.next P p q) = IntegralMixedVirtualTaskBits.saved P q := by
  unfold IntegralMixedVirtualTaskBits.saved
  rw [IntegralCriticalFlatEulerBits.next_root, IntegralCriticalFlatEulerBits.next_birth, IntegralCriticalFlatEulerBits.next_get]

theorem moment_next (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    momentValue P F (IntegralCriticalFlatEulerBits.next P p q) = momentValue P F q := by
  rw [moment_snapshot, moment_snapshot]
  apply momentAt_congr
  · exact saved_next P p q
  · exact IntegralCriticalFlatEulerBits.next_get P p q .row
  · exact IntegralCriticalFlatEulerBits.next_get P p q .col
  · exact IntegralCriticalFlatEulerBits.next_get P p q .slot11
  · exact IntegralCriticalFlatEulerBits.next_get P p q .slot12
  · exact IntegralCriticalFlatEulerBits.next_modulus P p q

def momentTask (P : Parameters) (z : List Bool) : List Bool :=
  IntegralCriticalFlatEulerBits.next P .factorPower (IntegralCriticalFlatBerkowitzQuery.momentWriter P z)

theorem momentTask_FP (P : Parameters) (a : Access P) : momentTask P ∈ FP :=
  mem_FP_comp (IntegralCriticalFlatBerkowitzQuery.momentWriter_FP P a) (IntegralCriticalFlatEulerBits.next_FP P a .factorPower)

theorem momentTask_root (P : Parameters) (z : List Bool) :
    RankedHistoryTask.root (momentTask P z) = RankedHistoryTask.root (original z) := by
  unfold momentTask
  rw [IntegralCriticalFlatEulerBits.next_root, IntegralCriticalFlatBerkowitzQuery.momentWriter_root]

theorem momentTask_birth (P : Parameters) (z : List Bool) : birth P (momentTask P z) = birth P (original z) := by
  unfold momentTask
  rw [IntegralCriticalFlatEulerBits.next_birth, IntegralCriticalFlatBerkowitzQuery.momentWriter_birth]

theorem momentTask_phase (P : Parameters) (z : List Bool) : phase (momentTask P z) = 4 :=
  IntegralCriticalFlatEulerBits.next_phase P .factorPower _

theorem momentTask_routine (P : Parameters) (z : List Bool) :
    IntegralMixedRoutineTaskBits.routine P (momentTask P z) = IntegralMixedRoutineTaskBits.routine P (original z) := by
  unfold IntegralMixedRoutineTaskBits.routine momentTask
  rw [IntegralCriticalFlatEulerBits.next_get, IntegralCriticalFlatBerkowitzQuery.momentWriter_get]
  rfl

theorem momentTask_frame (P : Parameters) (z : List Bool) (hp : 4 < phase (original z)) :
    IntegralMixedRoutineTaskBits.Frame P (original z) (momentTask P z) := by
  have HT := IntegralCriticalFlatEulerBits.next_tasks P .factorPower (original z)
    (IntegralCriticalFlatBerkowitzQuery.momentWriter P z)
    (IntegralCriticalFlatBerkowitzQuery.momentWriter_tasks P (original z) z (tasks_self P (original z)))
  have HR := IntegralMixedRoutineTaskBits.lower_phase P (original z) (momentTask P z)
    (momentTask_birth P z) (momentTask_routine P z) (by rw [momentTask_phase]; exact hp)
  change Tasks P (original z) (momentTask P z) at HT
  rcases HT with HE | HT
  · rw [HE] at HR
    exact False.elim (Nat.lt_irrefl _ HR)
  · exact ⟨HT.1, HT.2, HR⟩

theorem momentTask_value_bounded (P : Parameters) (F : Family) (z : List Bool)
    (hr : Nat.fromBitsLE (basisRowCode z) ≤ numericCap P (RankedHistoryTask.root (original z)))
    (ht : Nat.fromBitsLE (basisColCode z) ≤ numericCap P (RankedHistoryTask.root (original z)))
    (hs : Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex z) ≤ numericCap P (RankedHistoryTask.root (original z)))
    (hu : Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex z) ≤ numericCap P (RankedHistoryTask.root (original z))) :
    momentValue P F (momentTask P z) = (momentFamily (source P F)).value z :=
  (moment_next P F .factorPower _).trans (moment_child_bounded P F z hr ht hs hu)

theorem relative_moment_child (P : Parameters) (F : Family) (q : List Bool) :
    momentValue P F (momentTask P (outerPacket (source P F) (IntegralCriticalFlatRelativeFactorBits.packet P q))) =
      (momentFamily (source P F)).value (outerPacket (source P F) (IntegralCriticalFlatRelativeFactorBits.packet P q)) := by
  apply momentTask_value_bounded
  · simp only [outerPacket, IntegralCriticalFlatRelativeFactorBits.packet, basisRowCode,
      IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.rowIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    change get P .row q % 1 ≤ _
    simp only [Nat.mod_one, Nat.zero_le]
  · simp only [outerPacket, IntegralCriticalFlatRelativeFactorBits.packet, basisColCode,
      IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.colIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    change get P .col q % 1 ≤ _
    simp only [Nat.mod_one, Nat.zero_le]
  · simp only [outerPacket, IntegralCriticalFlatRelativeFactorBits.packet,
      IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.rowIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (Nat.div_le_self _ _).trans (get_le P .row q)
  · simp only [outerPacket, IntegralCriticalFlatRelativeFactorBits.packet,
      IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.colIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (Nat.div_le_self _ _).trans (get_le P .col q)

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
