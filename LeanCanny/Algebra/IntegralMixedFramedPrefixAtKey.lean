/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFamilyRunView
/-! # Actual saved-key prefix readback at its literal chronological birth

These are equalities of actual scalar prefixes, including their row systems
and coefficient algebra. No replay at a different spatial source occurs.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPrefixAtKey
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family keyAt prefixLength)
open IntegralMixedFramedFamilyRunView (runAt)

private theorem prefix_congr (P : Parameters) (D : Plan P) (r s : List Bool) (i j : ℕ)
    (hr : r=s) (hi : i=j) (hb : i≤P.cap r+1) (hc : j≤P.cap s+1) :
    HEq (runAt P D r i hb).sampler.scalarPrefix (runAt P D s j hc).sampler.scalarPrefix := by
  cases hr
  cases hi
  rfl

theorem prefix_view (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    HEq ((family P D H).state key).sampler.scalarPrefix
      (runAt P D (pairFst key) (prefixLength P key) (min_le_right _ _)).sampler.scalarPrefix := HEq.rfl

theorem at_key (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (root context : List Bool) (birth : ℕ) (hb : birth≤P.cap root+1) :
    HEq ((family P D H).state (keyAt root birth context)).sampler.scalarPrefix
      (runAt P D root birth hb).sampler.scalarPrefix :=
  (prefix_view P D H _).trans (prefix_congr P D _ _ _ _ (IntegralMixedFramedHistoryFamilyBits.keyAt_root root birth context)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root birth context hb) _ hb)

theorem at_saved (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (hb : birth P c≤P.cap (RankedHistoryTask.root c)+1) :
    HEq ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix
      (runAt P D (RankedHistoryTask.root c) (birth P c) hb).sampler.scalarPrefix :=
  (prefix_view P D H _).trans (prefix_congr P D _ _ _ _ (IntegralMixedFullHistoryFamilyBits.saved_root P c)
    (IntegralMixedFullHistoryFamilyBits.saved_prefix P c) _ hb)

end LeanCanny.Algebra.IntegralMixedFramedPrefixAtKey
