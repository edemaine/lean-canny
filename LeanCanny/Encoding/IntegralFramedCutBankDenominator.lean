/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutAcceptedRoot
public import LeanCanny.Algebra.IntegralMixedFramedHistoryProducer
/-! # The actual newest bank denominator is the relative normalization leading

The original root, creating birth and context are preserved literally.
The leading is the integer normalization denominator over the actual old
prefix basis, not the raw specialized factor leading.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutBankDenominator
open LeanCanny.Algebra IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family instruction selection keyAt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem cut_leading (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (hcut : IntegralFramedCreatingCut.IsCut (instruction P D key).command) :
    IntegralMixedFramedCompanionBits.leading P D H key=
      IntegralRelativeLeadingNormalization.denominator ((family P D H).state key).sampler.scalarPrefix.basis.finBasis
        ((IntegralRelativeTruncation.truncate (IntegralMixedRelativeCuts.factor ((family P D H).state key)
          ((family P D H).birth_bound key) ((family P D H).rule key) ((family P D H).kind key))
            ((family P D H).degree key)).coeff ((family P D H).degree key)) := by
  cases hc:(instruction P D key).command with
  | integer p hp hd => simp only [hc,IntegralFramedCreatingCut.IsCut] at hcut
  | critical r => simp only [hc,IntegralFramedCreatingCut.IsCut] at hcut
  | cut r k d ha hd =>
    have HS : selection P D H key=⟨r,k,d,ha⟩ := by
      unfold selection
      rw [hc]
    unfold IntegralMixedFramedCompanionBits.leading
    change IntegralMixedFullHistoryScript.leading ((family P D H).state key) ((family P D H).birth_bound key)
      (instruction P D key).command=
      IntegralRelativeLeadingNormalization.denominator ((family P D H).state key).sampler.scalarPrefix.basis.finBasis
        ((IntegralRelativeTruncation.truncate (IntegralMixedRelativeCuts.factor ((family P D H).state key)
          ((family P D H).birth_bound key) (selection P D H key).rule (selection P D H key).kind)
            (selection P D H key).degree).coeff (selection P D H key).degree)
    rw [hc,HS]
    rfl

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralMixedFramedCompanionBits.leading

theorem newest_leading (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P c) :
    ((family P D H).state (IntegralFramedCutSuccessor.key P c)).bank.denominator
      ⟨0,IntegralFramedCutSuccessor.positive P D H c⟩=
        IntegralMixedFramedCompanionBits.leading P D H (IntegralMixedVirtualTaskBits.saved P c) := by
  have HC : IntegralMixedFramedHistoryFamilyBits.prefixLength P (IntegralFramedCutSuccessor.key P c)=birth P c+1 :=
    (IntegralMixedFramedHistoryFamilyBits.family_birth P D H _).symm.trans (IntegralFramedCutSuccessor.active_count P D H c ha)
  have HR : pairFst (IntegralFramedCutSuccessor.key P c)=RankedHistoryTask.root c :=
    IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _
  have HB : IntegralMixedFramedHistoryFamilyBits.prefixLength P (IntegralFramedCutSuccessor.key P c)-1-0=birth P c := by
    rw [HC]
    omega
  have HK : keyAt (pairFst (IntegralFramedCutSuccessor.key P c))
      (IntegralMixedFramedHistoryFamilyBits.prefixLength P (IntegralFramedCutSuccessor.key P c)-1-0)
        (BinaryNatCode.encode (get P .slot15 c))=IntegralMixedVirtualTaskBits.saved P c :=
    congrArg₂ (fun root b=>keyAt root b (BinaryNatCode.encode (get P .slot15 c))) HR HB
  have HL : ((family P D H).state (IntegralFramedCutSuccessor.key P c)).bank.denominator
      ⟨0,IntegralFramedCutSuccessor.positive P D H c⟩=
      IntegralMixedFramedCompanionBits.leading P D H
        (keyAt (pairFst (IntegralFramedCutSuccessor.key P c))
          (IntegralMixedFramedHistoryFamilyBits.prefixLength P (IntegralFramedCutSuccessor.key P c)-1-0)
            (BinaryNatCode.encode (get P .slot15 c))) := by
    unfold IntegralMixedFramedCompanionBits.leading
    exact IntegralMixedFramedHistoryFamilyBits.retained_leading_key P D H (IntegralFramedCutSuccessor.key P c)
      ⟨0,IntegralFramedCutSuccessor.positive P D H c⟩ (BinaryNatCode.encode (get P .slot15 c))
  rw [HK] at HL
  exact HL

theorem newest_denominator (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P c) (hcut : IntegralFramedCreatingCut.ParentCut P D c) :
    ((family P D H).state (IntegralFramedCutSuccessor.key P c)).bank.denominator
      ⟨0,IntegralFramedCutSuccessor.positive P D H c⟩=
      IntegralRelativeLeadingNormalization.denominator
        ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.basis.finBasis
        ((IntegralRelativeTruncation.truncate
          (IntegralMixedRelativeCuts.factor ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
            ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c))
            ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c)))
              ((family P D H).degree (IntegralMixedVirtualTaskBits.saved P c))).coeff
                ((family P D H).degree (IntegralMixedVirtualTaskBits.saved P c))) :=
  (newest_leading P D H c ha).trans (cut_leading P D H (IntegralMixedVirtualTaskBits.saved P c) hcut)

end LeanCanny.Encoding.IntegralFramedCutBankDenominator
