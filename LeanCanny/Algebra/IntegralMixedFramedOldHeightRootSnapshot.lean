/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightSnapshot
public import LeanCanny.Algebra.IntegralMixedOldHeightQueryFields
/-! # Saved-birth snapshots of framed companion integer entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedHistoryScript IntegralMixedHistory
open IntegralMixedOldBankCofactorBits (Routing)
open IntegralMixedOldHeightBits (writer producerBirth radix)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def rootEntry (P : Parameters) (D : Plan P) (root : List Bool) (b r t : ℕ) : ℤ :=
  commandEntry P D root
    (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) (D.rules root) (min b (P.cap root + 1)))
    (by rw [paddedPast_length]; exact min_le_right _ _)
    ((chronological (D.rules root) (min b (P.cap root + 1))).getD (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root)) r t

theorem sourceEntry_root (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (r t : ℕ) : sourceEntry P D H key r t =
      rootEntry P D (pairFst key) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) r t := by
  rw [sourceEntry_command]
  unfold rootEntry
  apply commandEntry_congr
  · rfl
  · exact heq_of_eq (congrArg (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst key)) (D.rules (pairFst key)))
      (min_eq_left (min_le_right _ _ : IntegralMixedFramedHistoryFamilyBits.prefixLength P key ≤ P.cap (pairFst key) + 1)).symm)
  · exact heq_of_eq (congrArg (fun b => (chronological (D.rules (pairFst key)) b).getD (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst key)))
      (min_eq_left (min_le_right _ _ : IntegralMixedFramedHistoryFamilyBits.prefixLength P key ≤ P.cap (pairFst key) + 1)).symm)

theorem sourceEntry_invariance (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q c : List Bool) (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q) (r t : ℕ) :
    sourceEntry P D H (IntegralMixedVirtualTaskBits.saved P c) r t = sourceEntry P D H (IntegralMixedVirtualTaskBits.saved P q) r t := by
  rw [sourceEntry_root, sourceEntry_root]
  simp only [IntegralMixedFramedHistoryFamilyBits.prefixLength]
  rw [IntegralMixedFullHistoryFamilyBits.saved_root,
    IntegralMixedFullHistoryFamilyBits.saved_root, IntegralMixedFullHistoryFamilyBits.saved_prefix,
    IntegralMixedFullHistoryFamilyBits.saved_prefix, hr, hb]

noncomputable def companionInteger (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (R : Routing) (q : List Bool) : ℤ :=
  sourceEntry P D H (IntegralMixedVirtualTaskBits.saved P (writer P R q))
    (get P .row (writer P R q)) (get P .col (writer P R q))

theorem companionInteger_root (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (R : Routing) (q : List Bool) : companionInteger P D H R q =
    rootEntry P D (RankedHistoryTask.root q) (producerBirth P q) (get P .row q / radix P q) (get P .col q / radix P q) := by
  unfold companionInteger
  rw [sourceEntry_root]
  simp only [IntegralMixedFramedHistoryFamilyBits.prefixLength]
  rw [IntegralMixedFullHistoryFamilyBits.saved_root, IntegralMixedFullHistoryFamilyBits.saved_prefix,
    IntegralMixedOldHeightBits.writer_root, IntegralMixedOldHeightBits.writer_birth, IntegralMixedOldHeightBits.writer_row, IntegralMixedOldHeightBits.writer_col]

theorem origin_entry_root (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : Fin ((bankFamily P D H).birth key))
    (r t : Fin (FixedWidthPolynomial.count ((bankFamily P D H).birth key) ((bankFamily P D H).width key))) :
    let o := IntegralMixedFramedHistoryFamilyBits.origin P D H key i
    Algebra.leftMulMatrix (birthPrefix (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst key))
      (IntegralMixedFramedHistoryFamilyBits.commands P D key) (((bankFamily P D H).birth_bound key).trans (Nat.le_succ (P.cap (pairFst key) + 1))) i).basis.finBasis
      (AdjoinRoot.root _) (o.chain.oldIndex r) (o.chain.oldIndex t) =
    rootEntry P D (pairFst key) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key - 1 - i.val)
      (r.val / FixedWidthPolynomial.count i.val (P.width (pairFst key))) (t.val / FixedWidthPolynomial.count i.val (P.width (pairFst key))) := by
  refine (origin_entry P D H key i r t []).trans ?_
  have HB : IntegralMixedFramedHistoryFamilyBits.prefixLength P key - 1 - i.val ≤ P.cap (pairFst key) + 1 :=
    (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (min_le_right _ _))
  have HK := IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P (pairFst key)
    (IntegralMixedFramedHistoryFamilyBits.prefixLength P key - 1 - i.val) [] HB
  rw [sourceEntry_root, IntegralMixedFramedHistoryFamilyBits.keyAt_root, HK]
end LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
