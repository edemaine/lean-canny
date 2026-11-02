/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCompleteSuffixSaved
/-! # Sibling saved contexts keep the literal joint-root predicate

The original plan, root word and chronological prefix length determine
all scalar rows. Sampling labels and the tuple are unchanged.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedSiblingRoots
open LeanCanny.Algebra IntegralCriticalHistoryTask UniformIntegralPrefix
open IntegralMixedFramedHistoryFamilyBits (Plan family prefixLength)
open IntegralMixedFramedFamilyRunView (runAt)

private theorem run_roots_congr (P : Parameters) (D : Plan P) (r s : List Bool) (a b : ℕ)
    (ha : a≤P.cap r+1) (hb : b≤P.cap s+1) (hr : r=s) (he : a=b) (z : ℕ→ℝ) :
    RootsAt (runAt P D r a ha).sampler.scalarPrefix z ↔ RootsAt (runAt P D s b hb).sampler.scalarPrefix z := by
  cases hr
  cases he
  rfl

theorem roots_sibling (P : Parameters) (D : Plan P)
    (H K : IntegralMixedFramedHistoryFamilyBits.Data P D) (u v : List Bool)
    (hr : pairFst u=pairFst v) (hb : prefixLength P u=prefixLength P v) (z : ℕ→ℝ) :
    RootsAt ((family P D H).state u).sampler.scalarPrefix z ↔
      RootsAt ((family P D K).state v).sampler.scalarPrefix z :=
  (IntegralFramedCompleteSuffixSaved.roots_at_word P D H u z).trans
    ((run_roots_congr P D _ _ _ _ (min_le_right _ _) (min_le_right _ _) hr hb z).trans
      (IntegralFramedCompleteSuffixSaved.roots_at_word P D K v z).symm)

end LeanCanny.Encoding.IntegralFramedSiblingRoots
