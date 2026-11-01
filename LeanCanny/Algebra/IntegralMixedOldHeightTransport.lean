/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOldHeightSnapshot
public import LeanCanny.Algebra.IntegralMixedOldHeightPass
/-! # Earlier creating companions are the literal blocks of old-height matrices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFullHistoryScript IntegralMixedHistory
open IntegralMixedOldBankCofactorBits (Routing)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem commandEntry_of_fin {n S B : ℕ} {F : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State F S B 0 ι) (cs : List (Command F B)) (h : cs.length ≤ S) (c : Command F B)
    (r t : Fin (FixedWidthPolynomial.count (cs.length + 1) B)) :
    commandEntry initial cs h c r.val t.val =
      Algebra.leftMulMatrix (UniformIntegralPrefix.step (run initial cs (h.trans (Nat.le_succ _))).sampler.scalarPrefix
        h (Nat.two_pow_pos B) (polynomial (run initial cs (h.trans (Nat.le_succ _))) h c)
        (degree (run initial cs (h.trans (Nat.le_succ _))) h c)).basis.finBasis (AdjoinRoot.root _) r t := by
  simp only [commandEntry, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt t.isLt]
  rfl

theorem origin_entry (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool)
    (i : Fin ((bankFamily P D).birth key))
    (r t : Fin (FixedWidthPolynomial.count ((bankFamily P D).birth key) ((bankFamily P D).width key))) :
    let o := IntegralMixedFullHistoryFamilyBits.origin P D key i
    Algebra.leftMulMatrix
      (birthPrefix (IntegralMixedFullHistoryFamilyBits.initial P D (pairFst key)) (IntegralMixedFullHistoryFamilyBits.commands P D key)
        (((bankFamily P D).birth_bound key).trans (Nat.le_succ _)) i).basis.finBasis
      (AdjoinRoot.root _) (o.chain.oldIndex r) (o.chain.oldIndex t) =
    rootEntry P D (pairFst key) (IntegralMixedFullHistoryFamilyBits.prefixLength P key - 1 - i.val)
      (r.val / FixedWidthPolynomial.count i.val (P.width (pairFst key)))
      (t.val / FixedWidthPolynomial.count i.val (P.width (pairFst key))) := by
  let o := IntegralMixedFullHistoryFamilyBits.origin P D key i
  have HM : (IntegralMixedFullHistoryFamilyBits.prefixLength P key - 1 - i.val) ≤ P.cap (pairFst key) + 1 :=
    (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (min_le_right _ _))
  calc
    _ = commandEntry (IntegralMixedFullHistoryFamilyBits.initial P D (pairFst key))
        (older (IntegralMixedFullHistoryFamilyBits.commands P D key) i)
        (older_bound _ (((bankFamily P D).birth_bound key).trans (Nat.le_succ _)) i)
        (chosen (IntegralMixedFullHistoryFamilyBits.commands P D key) i)
        (o.chain.oldIndex r).val (o.chain.oldIndex t).val :=
      (commandEntry_of_fin _ _ _ _ (o.chain.oldIndex r) (o.chain.oldIndex t)).symm
    _ = _ := by
      rw [o.oldIndex_val r, o.oldIndex_val t]
      unfold rootEntry
      apply commandEntry_congr
      · exact (paddedPast_older (D.rules (pairFst key)) (IntegralMixedFullHistoryFamilyBits.prefixLength P key) i).trans
          (congrArg (paddedPast (D.rules (pairFst key))) (min_eq_left HM).symm)
      · exact (IntegralMixedFullHistoryFamilyBits.origin_command P D key i).trans
          (congrArg (fun b => (chronological (D.rules (pairFst key)) b).getD defaultCommand) (min_eq_left HM).symm)

theorem companionInteger_root (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing) (q : List Bool) :
    companionInteger P D R q = rootEntry P D (RankedHistoryTask.root q) (producerBirth P q)
      (get P .row q / radix P q) (get P .col q / radix P q) := by
  change sourceEntry P D (IntegralMixedVirtualTaskBits.saved P (writer P R q))
    (get P .row (writer P R q)) (get P .col (writer P R q)) = _
  rw [sourceEntry_root, IntegralMixedFullHistoryFamilyBits.saved_root, IntegralMixedFullHistoryFamilyBits.saved_prefix,
    writer_root, writer_birth, writer_row, writer_col]

end LeanCanny.Algebra.IntegralMixedOldHeightBits
