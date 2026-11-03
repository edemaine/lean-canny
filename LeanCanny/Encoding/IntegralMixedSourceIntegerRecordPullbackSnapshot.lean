/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullbackCells
public import LeanCanny.Algebra.IntegralMixedCausalPlanRootPullback
/-! # Original rule snapshots survive an honest caller-root projection -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullback
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ)
  (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (S root 0).degree≤2^P.width root)
  (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
  (hW : ∀root,(P.degree root).size≤P.sourceWidth root)
  (project : List Bool→List Bool) (extra : List Bool→ℕ)
local notation "D" => IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom
local notation "J" => IntegralMixedSourceIntegerRecordAppend.data P S hn hd hcap N hq T hz hT hroom hW
local notation "PP" => IntegralMixedFramedRootPullback.parameters P project extra
local notation "DD" => IntegralMixedFramedRootPullback.plan P D project extra
local notation "JJ" => IntegralMixedFramedRootPullback.data P D J project extra

include hq in
private theorem physical_row (key : List Bool) (i : ℕ) (hi : i<(PP).ambient (pairFst key)+1) :
    (IntegralMixedFramedPhysicalBits.rule PP DD key).heights ⟨i,hi⟩=
      IntegralMixedSourceIntegerRecordAppend.rowValue P N true (IntegralMixedFramedRootPullback.key project key) i := by
  have ho : i<P.ambient (pairFst (IntegralMixedFramedRootPullback.key project key))+1 := by
    rw [IntegralMixedFramedRootPullback.key_root]
    exact hi
  have H:=IntegralMixedCriticalRuleNatural.height_heq _ _
    (congrArg P.ambient (IntegralMixedFramedRootPullback.key_root project key).symm)
    (IntegralMixedFramedRootPullback.physical_rule_heq P D project extra key) i
  simp only [IntegralMixedCriticalRuleNatural.height,dite_eq_left (show i<P.ambient (project (pairFst key))+1 from hi),dite_eq_left ho] at H
  exact H.trans (IntegralMixedSourceIntegerRecordAppend.physical_row P S hn hd hcap N hq T hz hT hroom _ ⟨i,ho⟩)

private theorem virtual_row (key : List Bool) (i : ℕ) (hi : i<(PP).ambient (pairFst key)+1) :
    ((IntegralMixedFramedHistoryFamilyBits.family PP DD JJ).rule key).critical.heights ⟨i,hi⟩=
      IntegralMixedSourceIntegerRecordAppend.rowValue P N false (IntegralMixedFramedRootPullback.key project key) i := by
  have ho : i<P.ambient (pairFst (IntegralMixedFramedRootPullback.key project key))+1 := by
    rw [IntegralMixedFramedRootPullback.key_root]
    exact hi
  have HS:=IntegralMixedFramedRootPullback.virtual_rule_heq P D J project extra key
  have HC:=IntegralMixedFramedRootPullback.sweep_pred
    (fun n r=>HEq r.critical ((IntegralMixedFramedHistoryFamilyBits.family P D J).rule
      (IntegralMixedFramedRootPullback.key project key)).critical) _ _
    (congrArg P.ambient (IntegralMixedFramedRootPullback.key_root project key).symm) HS (HEq.rfl)
  have HH:=IntegralMixedCriticalRuleNatural.height_heq _ _
    (congrArg P.ambient (IntegralMixedFramedRootPullback.key_root project key).symm) HC i
  simp only [IntegralMixedCriticalRuleNatural.height,dite_eq_left (show i<P.ambient (project (pairFst key))+1 from hi),dite_eq_left ho] at HH
  exact HH.trans (IntegralMixedSourceIntegerRecordAppend.virtual_row P S hn hd hcap N hq T hz hT hroom hW _ ⟨i,ho⟩)

include hq in
theorem physical_mask (key : List Bool) (i : ℕ) (hi : i<(PP).ambient (pairFst key)+1) :
    (IntegralMixedFramedPhysicalBits.rule PP DD key).scales ⟨i,hi⟩=
      if (IntegralMixedSourceIntegerRecordAppend.mask P N true (IntegralMixedFramedRootPullback.key project key))[i]?.getD false then 2 else 1 := by
  have ho : i<P.ambient (pairFst (IntegralMixedFramedRootPullback.key project key))+1 := by
    rw [IntegralMixedFramedRootPullback.key_root]
    exact hi
  have H:=IntegralMixedCriticalRuleNatural.scale_heq _ _
    (congrArg P.ambient (IntegralMixedFramedRootPullback.key_root project key).symm)
    (IntegralMixedFramedRootPullback.physical_rule_heq P D project extra key) i
  simp only [IntegralMixedCriticalRuleNatural.scale,
    dite_eq_left (show i<P.ambient (project (pairFst key))+1 from hi),dite_eq_left ho] at H
  exact H.trans (IntegralMixedSourceIntegerRecordAppend.physical_mask P S hn hd hcap N hq T hz hT hroom _ ⟨i,ho⟩)

theorem virtual_mask (key : List Bool) (i : ℕ) (hi : i<(PP).ambient (pairFst key)+1) :
    ((IntegralMixedFramedHistoryFamilyBits.family PP DD JJ).rule key).critical.scales ⟨i,hi⟩=
      if (IntegralMixedSourceIntegerRecordAppend.mask P N false (IntegralMixedFramedRootPullback.key project key))[i]?.getD false then 2 else 1 := by
  have ho : i<P.ambient (pairFst (IntegralMixedFramedRootPullback.key project key))+1 := by
    rw [IntegralMixedFramedRootPullback.key_root]
    exact hi
  have HS:=IntegralMixedFramedRootPullback.virtual_rule_heq P D J project extra key
  have HC:=IntegralMixedFramedRootPullback.sweep_pred
    (fun n r=>HEq r.critical ((IntegralMixedFramedHistoryFamilyBits.family P D J).rule
      (IntegralMixedFramedRootPullback.key project key)).critical) _ _
    (congrArg P.ambient (IntegralMixedFramedRootPullback.key_root project key).symm) HS (HEq.rfl)
  have H:=IntegralMixedCriticalRuleNatural.scale_heq _ _
    (congrArg P.ambient (IntegralMixedFramedRootPullback.key_root project key).symm) HC i
  simp only [IntegralMixedCriticalRuleNatural.scale,
    dite_eq_left (show i<P.ambient (project (pairFst key))+1 from hi),dite_eq_left ho] at H
  exact H.trans (IntegralMixedSourceIntegerRecordAppend.virtual_mask P S hn hd hcap N hq T hz hT hroom hW _ ⟨i,ho⟩)

attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralMixedVirtualTaskBits.saved
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  rowQuery IntegralMixedSourceIntegerRecordAppend.rowSyntax

theorem word_eq (q : List Bool) : word P N project extra q=IntegralMixedAffineCode.encode
    (IntegralMixedFramedScalarCellsBits.affine PP DD JJ q) := by
  unfold word
  by_cases hi : get PP .slot8 q<IntegralMixedOriginalRuleBodyBits.arity PP q
  · rw [ite_eq_left hi]
    unfold IntegralMixedSourceIntegerRecordAppend.rowSyntax rowQuery
    simp only [pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    apply congrArg IntegralMixedAffineCode.encode
    unfold IntegralMixedFramedScalarCellsBits.affine
    dsimp only
    change get PP .slot8 q<(PP).ambient (pairFst (IntegralMixedVirtualTaskBits.saved PP q))+1 at hi
    rw [dite_eq_left hi]
    by_cases hx : get PP .slot15 q=1
    · rw [IntegralMixedFramedScalarCellsBits.rule_physical PP _ _ q hx]
      simp only [hx,decide_true]
      exact (physical_row P S hn hd hcap N hq T hz hT hroom project extra _ _ hi).symm
    · rw [IntegralMixedFramedScalarCellsBits.rule_virtual PP _ _ q hx]
      simp only [hx,decide_false]
      exact (virtual_row P S hn hd hcap N hq T hz hT hroom hW project extra _ _ hi).symm
  · rw [ite_eq_right hi]
    apply congrArg IntegralMixedAffineCode.encode
    unfold IntegralMixedFramedScalarCellsBits.affine
    dsimp only
    change ¬get PP .slot8 q<(PP).ambient (pairFst (IntegralMixedVirtualTaskBits.saved PP q))+1 at hi
    rw [dite_eq_right hi]

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullback
