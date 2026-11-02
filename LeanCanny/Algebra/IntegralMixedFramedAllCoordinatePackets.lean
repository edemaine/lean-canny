/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedAllCoordinateSource
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQCutProbes
public import LeanCanny.Algebra.IntegralMixedFramedCutProbePackets
public import LeanCanny.Algebra.IntegralMixedFramedAllCoordinateTransport
/-! # Arbitrary-modulus packets for unrestricted coordinate-Y coefficients -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedAllCoordinatePacketBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCutProbeTaskBits (original callerModulus row col coefficient)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralMixedCutMatrix.coefficientMatrix

abbrev oldRank := IntegralMixedFramedCutProbePacketBits.oldRank
noncomputable def Labels (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : Prop :=
  IntegralMixedFramedAllCoordinateSourceBits.Active P D H (original q) ∧
    coefficient P q<2^P.width (RankedHistoryTask.root (original q)) ∧ row q<oldRank P q ∧ col q<oldRank P q
theorem labels_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H)) : FPPred (Labels P D H) :=
  ((IntegralMixedFramedAllCoordinateSourceBits.active_FP P a D H I).comp IntegralMixedFramedCutProbeTaskBits.original_FP).and
    (((IntegralMixedFramedCutProbeTaskBits.coefficient_binary P a).lt
      ((BinaryFn.const 2).powUnary (a.width.comp (mem_FP_comp IntegralMixedFramedCutProbeTaskBits.original_FP RankedHistoryTask.root_FP)))).and
      ((IntegralMixedFramedCutProbeTaskBits.row_binary.lt (IntegralMixedFramedCutProbePacketBits.oldRank_binary P a)).and
        (IntegralMixedFramedCutProbeTaskBits.col_binary.lt (IntegralMixedFramedCutProbePacketBits.oldRank_binary P a))))

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : List Bool :=
  residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
    ((IntegralMixedFramedAllCoordinateSourceBits.source P D H).matrix (original q)) (row q) (col q) : ZMod (callerModulus q))

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
    (q : List Bool) (hl : ¬Labels P D H q) : value P D H q=[] := by
  have HZ : IntegralCriticalTotalSnapshotBits.integerEntry
      ((IntegralMixedFramedAllCoordinateSourceBits.source P D H).matrix (original q)) (row q) (col q)=0 := by
    by_cases ha : IntegralMixedFramedAllCoordinateSourceBits.Active P D H (original q)
    · by_cases hk : coefficient P q<2^P.width (RankedHistoryTask.root (original q))
      · apply integerEntry_outside
        simpa only [IntegralMixedFramedAllCoordinateSourceBits.arity,IntegralMixedFramedAllCoordinateSourceBits.width,oldRank,IntegralMixedFramedCutProbePacketBits.oldRank] using
          (show ¬(row q<oldRank P q ∧ col q<oldRank P q) from fun hi=>hl ⟨ha,hk,hi⟩)
      · rw [IntegralMixedFramedAllCoordinateSourceBits.matrix_outside P D H _ (Nat.le_of_not_gt hk)]
        exact integerEntry_zero _ _
    · rw [IntegralMixedFramedAllCoordinateSourceBits.matrix_inactive P D H _ ha]
      exact integerEntry_zero _ _
  unfold value
  rw [HZ]
  simp only [Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

theorem query_selected (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (q : List Bool) (hl : Labels P D H q) :
    IntegralMixedCoordinateCoefficientNative.Selected (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (family (IntegralMixedFramedCutProbeTaskBits.parameters P L F C) (IntegralMixedFramedCutProbeTransportBits.plan P D L F C)
        (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
      (IntegralMixedFramedAllCoordinateTaskBits.query P L F C q) := by
  refine ⟨(IntegralMixedFramedAllCoordinateTaskBits.query_valid P L F C q).mpr hl.1.1.1,
    IntegralMixedFramedAllCoordinateTaskBits.query_routine P L F C q,
    IntegralMixedFramedAllCoordinateTaskBits.query_phase P L F C q,?_,
    IntegralMixedFramedAllCoordinateTaskBits.query_context P L F C q hl.1.1.2⟩
  rw [IntegralMixedFramedAllCoordinateTaskBits.query_choice P L F C q
    (hl.1.2.2.2.trans (IntegralMixedFramedCutProbeTaskBits.scalar_bound P L F C q)),
    IntegralMixedFramedAllCoordinateBoundsBits.query_choiceBound P D H L F C q hl.1.1.2]
  exact hl.1.2.2.1

theorem query_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (q : List Bool) (hl : Labels P D H q) :
    IntegralMixedFramedCoordinateProbeBits.value (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C)
      (IntegralMixedFramedAllCoordinateTaskBits.query P L F C q)=value P D H q := by
  rw [IntegralMixedFramedCoordinateProbeBits.selected_value _ _ _ _ (query_selected P D H L F C q hl)]
  unfold IntegralMixedCoordinateCoefficientValue.value
  rw [IntegralMixedFramedAllCoordinateTaskBits.query_modulus]
  have HK : get (IntegralMixedFramedCutProbeTaskBits.parameters P L F C) .coefficient
      (IntegralMixedFramedAllCoordinateTaskBits.query P L F C q)=coefficient P q := by
    simp only [IntegralMixedFramedAllCoordinateTaskBits.query_get,reduceCtorEq,ite_false]
    exact IntegralMixedFramedChoiceProbeTaskBits.query_coefficient P L F C q hl.2.1
  have HR : get (IntegralMixedFramedCutProbeTaskBits.parameters P L F C) .row
      (IntegralMixedFramedAllCoordinateTaskBits.query P L F C q)=row q := by
    simp only [IntegralMixedFramedAllCoordinateTaskBits.query_get,reduceCtorEq,ite_false]
    exact IntegralMixedFramedChoiceProbeTaskBits.query_row P L F C q hl.2.2.1
  have HC : get (IntegralMixedFramedCutProbeTaskBits.parameters P L F C) .col
      (IntegralMixedFramedAllCoordinateTaskBits.query P L F C q)=col q := by
    simp only [IntegralMixedFramedAllCoordinateTaskBits.query_get,reduceCtorEq,ite_false]
    exact IntegralMixedFramedChoiceProbeTaskBits.query_col P L F C q hl.2.2.2
  rw [HK,HR,HC]
  unfold value
  rw [IntegralMixedFramedAllCoordinateSourceBits.matrix_active P D H _ hl.1]
  have HE:=IntegralMixedFramedAllCoordinateTransportBits.entry P D H L F C q hl.1.1.2
    (IntegralMixedFramedAllCoordinateBoundsBits.coordinate_cap P L F C q hl.1.2.1)
    (hl.1.2.2.2.trans (IntegralMixedFramedCutProbeTaskBits.scalar_bound P L F C q)) (coefficient P q) (row q) (col q)
  exact congrArg (fun z : ℤ=>residueBits (z : ZMod (callerModulus q))) HE

end LeanCanny.Algebra.IntegralMixedFramedAllCoordinatePacketBits
