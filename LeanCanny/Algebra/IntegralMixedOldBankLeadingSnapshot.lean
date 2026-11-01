/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOldHeightSnapshot
public import LeanCanny.Algebra.IntegralMixedProducerLeadingActual
/-! # Literal retained leading values at actual earlier mixed producer queries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOldBankLeadingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFullHistoryScript IntegralMixedHistory
open IntegralMixedOldHeightBits (bankFamily)
open IntegralMixedOldBankCofactorBits (Routing)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def commandLeading {n S B : ℕ} {F : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State F S B 0 ι) (cs : List (Command F B)) (h : cs.length ≤ S) (c : Command F B) : ℤ :=
  IntegralMixedFullHistoryScript.leading (run initial cs (h.trans (Nat.le_succ _))) h c

theorem commandLeading_congr {n S B : ℕ} {F : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State F S B 0 ι) (cs ds : List (Command F B)) (h : cs.length ≤ S) (hd : ds.length ≤ S)
    (c e : Command F B) (hcs : cs = ds) (hc : c = e) :
    commandLeading initial cs h c = commandLeading initial ds hd e := by
  cases hcs
  cases hc
  rfl

noncomputable def rootLeading (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (root : List Bool) (b : ℕ) :=
  commandLeading (IntegralMixedFullHistoryFamilyBits.initial P D root)
    (paddedPast (D.rules root) (min b (P.cap root + 1)))
    (by rw [paddedPast_length]; exact min_le_right _ _)
    ((chronological (D.rules root) (min b (P.cap root + 1))).getD defaultCommand)

theorem leading_root (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) :
    IntegralMixedFullHistoryCompanionBits.leading P D key =
      rootLeading P D (pairFst key) (IntegralMixedFullHistoryFamilyBits.prefixLength P key) := by
  change commandLeading (IntegralMixedFullHistoryFamilyBits.initial P D (pairFst key))
    (IntegralMixedFullHistoryFamilyBits.commands P D key) ((bankFamily P D).birth_bound key)
    (IntegralMixedFullHistoryFamilyBits.creatingCommand P D key) = _
  unfold rootLeading
  apply commandLeading_congr
  · exact congrArg (paddedPast (D.rules (pairFst key)))
      (min_eq_left (min_le_right _ _ : IntegralMixedFullHistoryFamilyBits.prefixLength P key ≤ P.cap (pairFst key) + 1)).symm
  · exact congrArg (fun b => (chronological (D.rules (pairFst key)) b).getD defaultCommand)
      (min_eq_left (min_le_right _ _ : IntegralMixedFullHistoryFamilyBits.prefixLength P key ≤ P.cap (pairFst key) + 1)).symm

theorem retained_root (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool)
    (i : Fin ((bankFamily P D).birth key)) :
    ((bankFamily P D).state key).bank.denominator i =
      rootLeading P D (pairFst key) (IntegralMixedFullHistoryFamilyBits.prefixLength P key - 1 - i.val) := by
  have H := IntegralMixedFullHistoryFamilyBits.origin_denominator P D key i
  refine H.trans ?_
  change commandLeading (IntegralMixedFullHistoryFamilyBits.initial P D (pairFst key))
    (older (IntegralMixedFullHistoryFamilyBits.commands P D key) i)
    (older_bound _ (((bankFamily P D).birth_bound key).trans (Nat.le_succ _)) i)
    (chosen (IntegralMixedFullHistoryFamilyBits.commands P D key) i) = _
  have HM : (IntegralMixedFullHistoryFamilyBits.prefixLength P key - 1 - i.val) ≤ P.cap (pairFst key) + 1 :=
    (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (min_le_right _ _))
  unfold rootLeading
  apply commandLeading_congr
  · exact (paddedPast_older (D.rules (pairFst key)) (IntegralMixedFullHistoryFamilyBits.prefixLength P key) i).trans
      (congrArg (paddedPast (D.rules (pairFst key))) (min_eq_left HM).symm)
  · exact (IntegralMixedFullHistoryFamilyBits.origin_command P D key i).trans
      (congrArg (fun b => (chronological (D.rules (pairFst key)) b).getD defaultCommand) (min_eq_left HM).symm)

theorem child_leading (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing)
    (q : List Bool) (i : Fin (IntegralMixedOldBankCofactorBits.count P (bankFamily P D) q)) :
    IntegralMixedFullHistoryCompanionBits.leading P D (IntegralMixedVirtualTaskBits.saved P
      (IntegralMixedOldBankCofactorBits.writer P R (IntegralMixedOldBankCofactorBits.packet P (bankFamily P D) q i.val))) =
      ((bankFamily P D).state (IntegralMixedVirtualTaskBits.saved P q)).bank.denominator i := by
  rw [leading_root, IntegralMixedFullHistoryFamilyBits.saved_root, IntegralMixedFullHistoryFamilyBits.saved_prefix,
    IntegralMixedOldBankCofactorBits.writer_packet_birth P (bankFamily P D) (IntegralMixedFullHistoryFamilyBits.geometry P D) R q i.val i.isLt,
    IntegralMixedOldBankCofactorBits.writer_root]
  have H := retained_root P D (IntegralMixedVirtualTaskBits.saved P q) i
  simpa only [IntegralMixedOldBankCofactorBits.packet, pairFst_pair, IntegralMixedFullHistoryFamilyBits.saved_root,
    IntegralMixedFullHistoryFamilyBits.saved_prefix, IntegralMixedOldBankCofactorBits.count_eq P (bankFamily P D) (IntegralMixedFullHistoryFamilyBits.geometry P D)] using H.symm

end LeanCanny.Algebra.IntegralMixedOldBankLeadingBits
