/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCutProbeSource
public import LeanCanny.Algebra.IntegralMixedFramedCutProbeTransport
/-! # Arbitrary-modulus packets for full actual cut-coefficient matrices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCutProbePacketBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCutProbeTaskBits (original callerModulus row col coefficient)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralMixedCutMatrix.coefficientMatrix

def oldRank (P : Parameters) (q : List Bool) :=
  FixedWidthPolynomial.count (birth P (original q)) (P.width (RankedHistoryTask.root (original q)))
def Labels (P : Parameters) (q : List Bool) : Prop :=
  IntegralMixedFramedFullCutProbeBits.Active P (original q) ∧
    coefficient P q<2^P.width (RankedHistoryTask.root (original q)) ∧ row q<oldRank P q ∧ col q<oldRank P q

theorem oldRank_binary (P : Parameters) (a : Access P) : BinaryFn (oldRank P) :=
  ((BinaryFn.const 2).powUnary (a.width.comp (mem_FP_comp IntegralMixedFramedCutProbeTaskBits.original_FP RankedHistoryTask.root_FP))).powUnary
    ((IntegralMixedOldHeightBits.birth_unary P a).comp IntegralMixedFramedCutProbeTaskBits.original_FP)
theorem labels_FP (P : Parameters) (a : Access P) : FPPred (Labels P) :=
  ((IntegralMixedFramedFullCutProbeBits.active_FP P a).comp IntegralMixedFramedCutProbeTaskBits.original_FP).and
    (((IntegralMixedFramedCutProbeTaskBits.coefficient_binary P a).lt
      ((BinaryFn.const 2).powUnary (a.width.comp (mem_FP_comp IntegralMixedFramedCutProbeTaskBits.original_FP RankedHistoryTask.root_FP)))).and
      ((IntegralMixedFramedCutProbeTaskBits.row_binary.lt (oldRank_binary P a)).and
        (IntegralMixedFramedCutProbeTaskBits.col_binary.lt (oldRank_binary P a))))

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : List Bool :=
  residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
    ((IntegralMixedFramedCutProbeSourceBits.source P D H).matrix (original q)) (row q) (col q) : ZMod (callerModulus q))

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
      ((IntegralMixedFramedCutProbeSourceBits.source P D H).matrix (original q)) (row q) (col q)=0 := by
    by_cases ha : IntegralMixedFramedFullCutProbeBits.Active P (original q)
    · by_cases hk : coefficient P q<2^P.width (RankedHistoryTask.root (original q))
      · apply integerEntry_outside
        simpa only [IntegralMixedFramedCutProbeSourceBits.arity,IntegralMixedFramedCutProbeSourceBits.width,oldRank] using
          (show ¬(row q<oldRank P q ∧ col q<oldRank P q) from fun hi=>hl ⟨ha,hk,hi⟩)
      · rw [IntegralMixedFramedCutProbeSourceBits.matrix_outside P D H _ (Nat.le_of_not_gt hk)]
        exact integerEntry_zero _ _
    · rw [IntegralMixedFramedCutProbeSourceBits.matrix_inactive P D H _ ha]
      exact integerEntry_zero _ _
  unfold value
  rw [HZ]
  simp only [Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

private theorem source_coefficient (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (k : ℕ) :
    (IntegralMixedFramedCutSourceBits.source P D H).coefficient key k=
      IntegralMixedCutMatrix.coefficientMatrix ((family P D H).state key) ((family P D H).birth_bound key)
        ((family P D H).rule key) ((family P D H).kind key) k := by
  unfold IntegralMixedCutMatrix.coefficientMatrix
  rfl

theorem query_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (q : List Bool) (hl : Labels P q) :
    IntegralMixedFramedFullCutProbeBits.value (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C)
      (IntegralMixedFramedCutProbeTaskBits.query P L F C q)=value P D H q := by
  have hA : IntegralMixedFramedFullCutProbeBits.Active (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTaskBits.query P L F C q) :=
    ⟨(IntegralMixedFramedCutProbeTaskBits.query_valid P L F C q).mpr hl.1.1,
      IntegralMixedFramedCutProbeTaskBits.query_virtual_context P L F C q hl.1.2⟩
  rw [IntegralMixedFramedFullCutProbeBits.value,ite_eq_left hA,
    IntegralMixedFramedCutProbeTaskBits.query_modulus,
    IntegralMixedFramedCutProbeTaskBits.query_coefficient P L F C q hl.2.1,
    IntegralMixedFramedCutProbeTaskBits.query_row P L F C q hl.2.2.1,
    IntegralMixedFramedCutProbeTaskBits.query_col P L F C q hl.2.2.2]
  unfold value
  rw [IntegralMixedFramedCutProbeSourceBits.matrix_active P D H _ hl.1]
  have HE := IntegralMixedFramedCutProbeTransportBits.entry P D H L F C q hl.1.2 (coefficient P q) (row q) (col q)
  rw [source_coefficient] at HE
  exact congrArg (fun z : ℤ=>residueBits (z : ZMod (callerModulus q))) HE

end LeanCanny.Algebra.IntegralMixedFramedCutProbePacketBits
