/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedChoiceProbeSource
public import LeanCanny.Algebra.IntegralMixedFramedCutProbePackets
public import LeanCanny.Algebra.IntegralMixedFramedChoiceProbeTransport
/-! # Arbitrary-modulus packets for every finite cut choice of the same parent -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedChoiceProbePacketBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCutProbeTaskBits (original callerModulus row col coefficient)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralMixedCutMatrix.coefficientMatrix

abbrev Labels := IntegralMixedFramedCutProbePacketBits.Labels
abbrev oldRank := IntegralMixedFramedCutProbePacketBits.oldRank
theorem labels_FP (P : Parameters) (a : Access P) : FPPred (Labels P) := IntegralMixedFramedCutProbePacketBits.labels_FP P a

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : List Bool :=
  residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
    ((IntegralMixedFramedChoiceProbeSourceBits.source P D H).matrix (original q)) (row q) (col q) : ZMod (callerModulus q))

private theorem integerEntry_zero {n : ℕ} (r s : ℕ) :
    IntegralCriticalTotalSnapshotBits.integerEntry (0 : Matrix (Fin n) (Fin n) ℤ) r s=0 := by
  simp only [IntegralCriticalTotalSnapshotBits.integerEntry,Matrix.zero_apply,dite_eq_ite,ite_self]
private theorem integerEntry_outside {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r s : ℕ)
    (h : ¬(r<n ∧ s<n)) : IntegralCriticalTotalSnapshotBits.integerEntry M r s=0 := by
  by_cases hr : r<n
  · have hs : ¬s<n := fun hs=>h ⟨hr,hs⟩
    simp only [IntegralCriticalTotalSnapshotBits.integerEntry,dite_eq_left hr,dite_eq_right hs]
  · simp only [IntegralCriticalTotalSnapshotBits.integerEntry,dite_eq_right hr]

theorem value_outside (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hl : ¬Labels P q) : value P D H q=[] := by
  have HZ : IntegralCriticalTotalSnapshotBits.integerEntry
      ((IntegralMixedFramedChoiceProbeSourceBits.source P D H).matrix (original q)) (row q) (col q)=0 := by
    by_cases ha : IntegralMixedFramedFullCutProbeBits.Active P (original q)
    · by_cases hk : coefficient P q<2^P.width (RankedHistoryTask.root (original q))
      · apply integerEntry_outside
        simpa only [IntegralMixedFramedChoiceProbeSourceBits.arity,IntegralMixedFramedChoiceProbeSourceBits.width,oldRank,IntegralMixedFramedCutProbePacketBits.oldRank] using
          (show ¬(row q<oldRank P q ∧ col q<oldRank P q) from fun hi=>hl ⟨ha,hk,hi⟩)
      · rw [IntegralMixedFramedChoiceProbeSourceBits.matrix_outside P D H _ (Nat.le_of_not_gt hk)]
        exact integerEntry_zero _ _
    · rw [IntegralMixedFramedChoiceProbeSourceBits.matrix_inactive P D H _ ha]
      exact integerEntry_zero _ _
  unfold value
  rw [HZ]
  simp only [Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

theorem query_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (q : List Bool) (hl : Labels P q) :
    IntegralMixedFramedFullChoiceProbeBits.value (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C)
      (IntegralMixedFramedChoiceProbeTaskBits.query P L F C q)=value P D H q := by
  have hA : IntegralMixedFramedFullCutProbeBits.Active (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedChoiceProbeTaskBits.query P L F C q) :=
    ⟨(IntegralMixedFramedChoiceProbeTaskBits.query_valid P L F C q).mpr hl.1.1,
      IntegralMixedFramedChoiceProbeTaskBits.query_context P L F C q hl.1.2⟩
  rw [IntegralMixedFramedFullChoiceProbeBits.value,ite_eq_left hA,
    IntegralMixedFramedChoiceProbeTaskBits.query_modulus,
    IntegralMixedFramedChoiceProbeTaskBits.query_coefficient P L F C q hl.2.1,
    IntegralMixedFramedChoiceProbeTaskBits.query_row P L F C q hl.2.2.1,
    IntegralMixedFramedChoiceProbeTaskBits.query_col P L F C q hl.2.2.2]
  unfold value
  rw [IntegralMixedFramedChoiceProbeSourceBits.matrix_active P D H _ hl.1]
  have HE := IntegralMixedFramedChoiceProbeTransportBits.entry P D H L F C q hl.1.2 (coefficient P q) (row q) (col q)
  unfold IntegralMixedFramedChoiceCoefficientBits.coefficient at HE ⊢
  exact congrArg (fun z : ℤ=>residueBits (z : ZMod (callerModulus q))) HE

end LeanCanny.Algebra.IntegralMixedFramedChoiceProbePacketBits
