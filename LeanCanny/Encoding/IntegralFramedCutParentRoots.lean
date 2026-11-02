/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPrefixAtKey
public import LeanCanny.Algebra.IntegralMixedFramedPaddedRoots
public import LeanCanny.Encoding.IntegralFramedCutSuccessorInput
/-! # An actual successor joint tuple retains the exact saved parent tail

The root word and chronological birth are read back before transporting
rows. Every historical instruction keeps its own source.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutParentRoots
open LeanCanny.Algebra IntegralCriticalHistoryTask UniformIntegralPrefix
open IntegralMixedFramedHistoryFamilyBits (Plan family keyAt)
open IntegralMixedFramedFamilyRunView (runAt)
open IntegralMixedFramedHistoryScript
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

theorem roots_at_key (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (root context : List Bool) (birth : ℕ) (hb : birth≤P.cap root+1) (z : ℕ→ℝ) :
    RootsAt ((family P D H).state (keyAt root birth context)).sampler.scalarPrefix z ↔
      RootsAt (runAt P D root birth hb).sampler.scalarPrefix z := by
  have HS : (family P D H).cap (keyAt root birth context)=P.cap root+1 := by
    unfold family
    change P.cap (pairFst (keyAt root birth context))+1=P.cap root+1
    exact congrArg (fun r=>P.cap r+1) (IntegralMixedFramedHistoryFamilyBits.keyAt_root root birth context)
  have HN : 2^(family P D H).width (keyAt root birth context)=2^P.width root := by
    unfold family
    change 2^P.width (pairFst (keyAt root birth context))=2^P.width root
    exact congrArg (fun r=>2^P.width r) (IntegralMixedFramedHistoryFamilyBits.keyAt_root root birth context)
  have HM : (family P D H).birth (keyAt root birth context)=
      (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) (D.rules root) birth).length :=
    (IntegralMixedFramedHistoryFamilyBits.family_birth P D H _).trans
      ((IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root birth context hb).trans (paddedPast_length _ _ _).symm)
  exact rootsAt_heq _ _ HS HN HM (IntegralMixedFramedPrefixAtKey.at_key P D H root context birth hb) z

theorem parent (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P c) (z : ℕ→ℝ)
    (hz : RootsAt ((family P D H).state (IntegralFramedCutSuccessor.key P c)).sampler.scalarPrefix z) :
    RootsAt ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix (fun i=>z (i+1)) := by
  let root:=RankedHistoryTask.root c
  let b:=birth P c
  let context:=BinaryNatCode.encode (get P .slot15 c)
  have HB:=ha.1
  unfold IntegralMixedVirtualCaps.valid at HB
  change b<P.cap root at HB
  have hb : b≤P.cap root+1 := by omega
  have hn : b+1≤P.cap root+1 := by omega
  change RootsAt ((family P D H).state (keyAt root (b+1) context)).sampler.scalarPrefix z at hz
  have HNew:=(roots_at_key P D H root context (b+1) hn z).mp hz
  have HOld:=padded_roots_parent (IntegralMixedFramedHistoryFamilyBits.initial P D root)
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) (D.rules root) b hb z HNew
  change RootsAt ((family P D H).state (keyAt root b context)).sampler.scalarPrefix (fun i=>z (i+1))
  exact (roots_at_key P D H root context b hb (fun i=>z (i+1))).mpr HOld

end LeanCanny.Encoding.IntegralFramedCutParentRoots
