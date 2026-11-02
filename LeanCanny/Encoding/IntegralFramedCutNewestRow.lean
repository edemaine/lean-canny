/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutParentInterpretation
public import LeanCanny.Algebra.IntegralMixedFramedRowPolynomial
public import LeanCanny.Algebra.IntegralMixedFramedCompanionCellCongr
/-! # The successor's newest row is its actual creating companion equation

The row is transported as a whole polynomial. Auxiliary key context changes
neither the actual creating instruction nor its old coefficient algebra.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutNewestRow
open LeanCanny.Algebra IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCompanionBits (source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family PaddedIntegralRowBits.polynomial

private theorem eval_nat_heq {a b : ℕ} (p : MvPolynomial (Fin a) ℤ) (q : MvPolynomial (Fin b) ℤ)
    (hm : a=b) (hp : HEq p q) (z : ℕ→ℝ) :
    p.eval₂ (Int.castRingHom ℝ) (fun i=>z i.val)=q.eval₂ (Int.castRingHom ℝ) (fun i=>z i.val) := by
  cases hm
  have he:=eq_of_heq hp
  cases he
  rfl

private theorem positive (P : Parameters) (q : List Bool) :
    0<IntegralMixedFramedRowBits.count P (IntegralFramedCutSuccessor.key P) q := by
  rw [IntegralMixedFramedRowBits.count,IntegralFramedCutSuccessor.prefix_length]
  exact lt_min (Nat.succ_pos _) (Nat.succ_pos _)

private theorem selected_zero (P : Parameters) (q : List Bool) :
    IntegralMixedFramedRowBits.selected P (IntegralFramedCutSuccessor.key P) (fun _=>[]) q=0 := rfl

private theorem count_eq (P : Parameters) (c : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P c) :
    IntegralMixedFramedRowBits.count P (IntegralFramedCutSuccessor.key P) c=birth P c+1 := by
  rw [IntegralMixedFramedRowBits.count,IntegralFramedCutSuccessor.prefix_length]
  apply min_eq_left
  have HB:=ha.1
  unfold IntegralMixedVirtualCaps.valid at HB
  omega

private theorem birth_eq (P : Parameters) (c : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P c) :
    IntegralMixedFramedRowBits.birth P (IntegralFramedCutSuccessor.key P) (fun _=>[]) c=birth P c := by
  unfold IntegralMixedFramedRowBits.birth
  rw [selected_zero,count_eq P c ha]
  omega

theorem source_row_root (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCutSuccessor.input P D H L F C hs) c w)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P c) :
    (PaddedIntegralRowBits.polynomial (source P D H) (fun key=>P.cap (pairFst key)+1)
      (IntegralMixedVirtualTaskBits.saved P c)).eval₂ (Int.castRingHom ℝ)
        (fun i=>IntegralFramedCutParentInterpretation.joint P D H L F C hs c w hv i.val)=0 := by
  let key:=IntegralFramedCutSuccessor.key P
  let index:List Bool→List Bool:=fun _=>[]
  let z:=IntegralFramedCutParentInterpretation.joint P D H L F C hs c w hv
  have HM : IntegralMixedFramedRowBits.count P key c=(family P D H).birth (key c) :=
    (IntegralMixedFramedHistoryFamilyBits.family_birth P D H (key c)).symm
  have HE:=eval_nat_heq _ _ HM (IntegralMixedFramedRowBits.polynomial_actual P D H key index (positive P) c) z
  have HR:=HE.trans ((IntegralFramedCutParentInterpretation.successor_roots P D H L F C hs c w hv)
    (IntegralMixedFramedRowBits.selectedIndex P D H key index (positive P) c))
  unfold IntegralMixedFramedRowBits.polynomial at HR
  rw [MvPolynomial.eval₂_rename] at HR
  have HF : ((fun j : Fin (IntegralMixedFramedRowBits.count P key c)=>z j.val) ∘
      BlockRenameCoefficient.shift ((source P D H).arity (IntegralMixedFramedRowBits.creatorKey P key index c)+1)
        (IntegralMixedFramedRowBits.count P key c) (IntegralMixedFramedRowBits.selected P key index c)
          (IntegralMixedFramedRowBits.row_fit P D H key index (positive P) c))=
      (fun i : Fin ((source P D H).arity (IntegralMixedFramedRowBits.creatorKey P key index c)+1)=>z i.val) := by
    funext i
    change z (IntegralMixedFramedRowBits.selected P key index c+i.val)=z i.val
    rw [selected_zero,Nat.zero_add]
  rw [HF] at HR
  have HK : pairFst (key c)=RankedHistoryTask.root c :=
    IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _
  have HRoot : pairFst (IntegralMixedFramedRowBits.creatorKey P key index c)=pairFst (IntegralMixedVirtualTaskBits.saved P c) :=
    (IntegralMixedFramedRowBits.creatorKey_root P key index c).trans
      (HK.trans (IntegralMixedFullHistoryFamilyBits.saved_root P c).symm)
  have HBirth : IntegralMixedFramedHistoryFamilyBits.prefixLength P (IntegralMixedFramedRowBits.creatorKey P key index c)=
      IntegralMixedFramedHistoryFamilyBits.prefixLength P (IntegralMixedVirtualTaskBits.saved P c) :=
    (IntegralMixedFramedRowBits.creatorKey_birth P key index c).trans
      ((birth_eq P c ha).trans (IntegralMixedFullHistoryFamilyBits.saved_prefix P c).symm)
  have HC : (source P D H).arity (IntegralMixedFramedRowBits.creatorKey P key index c)=birth P c :=
    (IntegralMixedFramedRowBits.creator_arity P D H key index c).trans (birth_eq P c ha)
  have HP : (source P D H).arity (IntegralMixedVirtualTaskBits.saved P c)=birth P c :=
    (IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth c
  have HA:=congrArg (fun n=>n+1) (HC.trans HP.symm)
  have HEval:=eval_nat_heq _ _ HA (IntegralMixedFramedCompanionBits.source_row_congr P D H _ _ HRoot HBirth) z
  exact HEval.symm.trans HR

end LeanCanny.Encoding.IntegralFramedCutNewestRow
