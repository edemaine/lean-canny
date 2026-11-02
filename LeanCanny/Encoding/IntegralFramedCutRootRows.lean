/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutParentRoots
public import LeanCanny.Encoding.IntegralFramedCutSourceRow
public import LeanCanny.Algebra.IntegralMixedFramedRowPolynomial
public import LeanCanny.Algebra.IntegralMixedFramedCompanionCellCongr
/-! # Actual successor row roots satisfy the creating normalized cut equations

The row is transported as a whole polynomial. Auxiliary key context changes
neither the actual creating instruction nor its old coefficient algebra.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutRootRows
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

theorem newest_source_row (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P c) (z : ℕ→ℝ)
    (hz : UniformIntegralPrefix.RootsAt ((family P D H).state (IntegralFramedCutSuccessor.key P c)).sampler.scalarPrefix z) :
    (PaddedIntegralRowBits.polynomial (source P D H) (fun key=>P.cap (pairFst key)+1)
      (IntegralMixedVirtualTaskBits.saved P c)).eval₂ (Int.castRingHom ℝ) (fun i=>z i.val)=0 := by
  let key:=IntegralFramedCutSuccessor.key P
  let index:List Bool→List Bool:=fun _=>[]
  have HM : IntegralMixedFramedRowBits.count P key c=(family P D H).birth (key c) :=
    (IntegralMixedFramedHistoryFamilyBits.family_birth P D H (key c)).symm
  have HE:=eval_nat_heq _ _ HM (IntegralMixedFramedRowBits.polynomial_actual P D H key index (positive P) c) z
  have HR:=HE.trans (hz (IntegralMixedFramedRowBits.selectedIndex P D H key index (positive P) c))
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

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (c : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P c) (z : ℕ→ℝ)
  (hz : UniformIntegralPrefix.RootsAt ((family P D H).state (IntegralFramedCutSuccessor.key P c)).sampler.scalarPrefix z)
local notation "G" => family P D H
local notation "parent" => IntegralMixedVirtualTaskBits.saved P c
local notation "old" => IntegralMixedCutSource.Family.state G parent
local notation "degree" => IntegralMixedCutSource.Family.degree G parent
local notation "p" => IntegralMixedHistory.normalizedScalarPolynomial old
  (IntegralMixedCutMatrix.raw old (IntegralMixedCutSource.Family.birth_bound G parent)
    (IntegralMixedCutSource.Family.rule G parent) (IntegralMixedCutSource.Family.kind G parent) degree) degree

include ha hz in
theorem normalized_rows (hcut : IntegralFramedCreatingCut.ParentCut P D c) :
    ∀ i,(UniformIntegralPrefixRows.rows ((G).cap parent) (old).sampler.scalarPrefix.rows (old).sampler.scalarPrefix.basis p degree i).eval₂
      (Int.castRingHom ℝ) (fun j=>z j.val)=0 := by
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · have HM : (IntegralMixedFramedCompanionBits.source P D H).arity parent+1=(G).birth parent+1 := rfl
    have HE:=eval_nat_heq _ _ HM (IntegralFramedCutSourceRow.cut_row P D H parent hcut) z
    exact HE.symm.trans (newest_source_row P D H c ha z hz)
  · simp only [UniformIntegralPrefixRows.rows,Fin.cons_succ,MvPolynomial.eval₂_rename]
    change ((old).sampler.scalarPrefix.rows j).eval₂ (Int.castRingHom ℝ) (fun k=>z (k.val+1))=0
    exact IntegralFramedCutParentRoots.parent P D H c ha z hz j

end LeanCanny.Encoding.IntegralFramedCutRootRows
