/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCompleteSuffix
/-! # Literal saved-key terminal roots retain actual selected-parent rows

Raw saved words need not equal their normalized key encoding. Their actual
prefixes are transported before any root/birth equality is applied.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCompleteSuffixSaved
open LeanCanny.Algebra IntegralCriticalHistoryTask UniformIntegralPrefix
open IntegralMixedFramedHistoryFamilyBits (Plan family keyAt prefixLength)
open IntegralMixedFramedFamilyRunView (runAt)
open IntegralMixedFramedHistoryScript
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

theorem roots_at_word (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (z : ℕ→ℝ) :
    RootsAt ((family P D H).state key).sampler.scalarPrefix z ↔
      RootsAt (runAt P D (pairFst key) (prefixLength P key) (min_le_right _ _)).sampler.scalarPrefix z := by
  have HS : (family P D H).cap key=P.cap (pairFst key)+1 := by unfold family; rfl
  have HN : 2^(family P D H).width key=2^P.width (pairFst key) := by unfold family; rfl
  have HM : (family P D H).birth key=
      (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst key)) (D.rules (pairFst key)) (prefixLength P key)).length :=
    (IntegralMixedFramedHistoryFamilyBits.family_birth P D H key).trans (paddedPast_length _ _ _).symm
  exact rootsAt_heq _ _ HS HN HM (IntegralMixedFramedPrefixAtKey.prefix_view P D H key) z

private theorem run_roots_congr (P : Parameters) (D : Plan P) (r s : List Bool) (a b : ℕ)
    (ha : a≤P.cap r+1) (hb : b≤P.cap s+1) (hr : r=s) (he : a=b) (z : ℕ→ℝ) :
    RootsAt (runAt P D r a ha).sampler.scalarPrefix z ↔ RootsAt (runAt P D s b hb).sampler.scalarPrefix z := by
  cases hr
  cases he
  rfl

theorem parent_roots (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c terminal : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
    (hroot : pairFst terminal=RankedHistoryTask.root c)
    (hfit : birth P c≤(family P D H).birth terminal) (z : ℕ→ℝ)
    (hz : RootsAt ((family P D H).state terminal).sampler.scalarPrefix z) :
    RootsAt ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix
      (fun i=>z (i+((family P D H).birth terminal-birth P c))) := by
  let root:=RankedHistoryTask.root c
  let b:=birth P c
  let newer:=(family P D H).birth terminal-b
  have HB:=ha.1
  unfold IntegralMixedVirtualCaps.valid at HB
  change b<P.cap root at HB
  have HM : (family P D H).birth terminal≤P.cap root+1 := by
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
    exact (min_le_right _ _).trans_eq (congrArg (fun r=>P.cap r+1) hroot)
  have HE : prefixLength P terminal=b+newer := by
    rw [←IntegralMixedFramedHistoryFamilyBits.family_birth P D H terminal]
    dsimp only [newer]
    omega
  have HNew:=(roots_at_word P D H terminal z).mp hz
  have HN:=(run_roots_congr P D (pairFst terminal) root (prefixLength P terminal) (b+newer)
    (min_le_right _ _) (by omega) hroot HE z).mp HNew
  have HOld:=padded_roots_suffix (IntegralMixedFramedHistoryFamilyBits.initial P D root)
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) (D.rules root) b newer (by omega) z HN
  change RootsAt ((family P D H).state (keyAt root b (BinaryNatCode.encode (get P .slot15 c)))).sampler.scalarPrefix _
  exact (IntegralFramedCutParentRoots.roots_at_key P D H root _ b (by omega) _).mpr HOld

end LeanCanny.Encoding.IntegralFramedCompleteSuffixSaved
