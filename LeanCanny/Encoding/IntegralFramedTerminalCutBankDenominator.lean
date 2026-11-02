/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutBankDenominator
/-! # The terminal retained cut denominator is its actual normalized producer leading -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutBankDenominator
open LeanCanny.Algebra IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family keyAt prefixLength)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralMixedFramedCompanionBits.leading

theorem index_lt (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c terminal : List Bool) (hfit : birth P c<(family P D H).birth terminal) :
    (family P D H).birth terminal-birth P c-1<(family P D H).birth terminal := by omega

theorem retained_leading (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c terminal : List Bool) (hroot : pairFst terminal=RankedHistoryTask.root c)
    (hfit : birth P c<(family P D H).birth terminal) :
    ((family P D H).state terminal).bank.denominator
      ⟨(family P D H).birth terminal-birth P c-1,index_lt P D H c terminal hfit⟩=
      IntegralMixedFramedCompanionBits.leading P D H (IntegralMixedVirtualTaskBits.saved P c) := by
  let i : Fin ((family P D H).birth terminal):=⟨(family P D H).birth terminal-birth P c-1,index_lt P D H c terminal hfit⟩
  have HB : prefixLength P terminal-1-i.val=birth P c := by
    rw [←IntegralMixedFramedHistoryFamilyBits.family_birth P D H terminal]
    dsimp only [i]
    omega
  have HK : keyAt (pairFst terminal) (prefixLength P terminal-1-i.val)
      (BinaryNatCode.encode (get P .slot15 c))=IntegralMixedVirtualTaskBits.saved P c :=
    congrArg₂ (fun root b=>keyAt root b (BinaryNatCode.encode (get P .slot15 c))) hroot HB
  have HL : ((family P D H).state terminal).bank.denominator i=
      IntegralMixedFramedCompanionBits.leading P D H
        (keyAt (pairFst terminal) (prefixLength P terminal-1-i.val) (BinaryNatCode.encode (get P .slot15 c))) := by
    unfold IntegralMixedFramedCompanionBits.leading
    exact IntegralMixedFramedHistoryFamilyBits.retained_leading_key P D H terminal i (BinaryNatCode.encode (get P .slot15 c))
  rw [HK] at HL
  exact HL

theorem retained_denominator (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c terminal : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
    (hcut : IntegralFramedCreatingCut.ParentCut P D c) (hroot : pairFst terminal=RankedHistoryTask.root c)
    (hfit : birth P c<(family P D H).birth terminal) :
    ((family P D H).state terminal).bank.denominator
      ⟨(family P D H).birth terminal-birth P c-1,index_lt P D H c terminal hfit⟩=
      IntegralRelativeLeadingNormalization.denominator
        ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.basis.finBasis
        ((IntegralRelativeTruncation.truncate
          (IntegralMixedRelativeCuts.factor ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
            ((family P D H).birth_bound _) ((family P D H).rule _) ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P c)))
              ((family P D H).degree (IntegralMixedVirtualTaskBits.saved P c))).coeff
                ((family P D H).degree (IntegralMixedVirtualTaskBits.saved P c))) :=
  (retained_leading P D H c terminal hroot hfit).trans
    ((IntegralFramedCutBankDenominator.newest_leading P D H c ha).symm.trans
      (IntegralFramedCutBankDenominator.newest_denominator P D H c ha hcut))

end LeanCanny.Encoding.IntegralFramedTerminalCutBankDenominator
