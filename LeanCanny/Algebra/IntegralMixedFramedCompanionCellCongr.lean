/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionKeyTransport
public import LeanCanny.Algebra.IntegralMixedFramedRowSource
/-! # Literal creating-source cells are independent of auxiliary key context

This concerns actual framed producer instructions. It does not assert
context coherence for arbitrary raw-cut fallback families.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCompanionBits
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
set_option backward.isDefEq.respectTransparency false

theorem source_cell_profile (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (source P D H).cell key=atPrefix P D (profile P key) := rfl

theorem source_cell_congr (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (u v : List Bool) (hr : pairFst u=pairFst v)
    (hb : IntegralMixedFramedHistoryFamilyBits.prefixLength P u=IntegralMixedFramedHistoryFamilyBits.prefixLength P v) :
    (source P D H).cell u=(source P D H).cell v :=
  (source_cell_profile P D H u).trans
    ((congrArg (atPrefix P D) (PrefixKey.ext _ _ hr hb)).trans (source_cell_profile P D H v).symm)

private theorem row_cell_congr (S T : PaddedIntegralGeneratorSource.Source) (s t : ℕ) (hS : S=T) (hs : s=t) :
    HEq (PaddedIntegralRowBits.polynomial S (fun _=>s) [])
      (PaddedIntegralRowBits.polynomial T (fun _=>t) []) := by
  cases hS
  cases hs
  rfl

theorem source_row_congr (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (u v : List Bool) (hr : pairFst u=pairFst v)
    (hb : IntegralMixedFramedHistoryFamilyBits.prefixLength P u=IntegralMixedFramedHistoryFamilyBits.prefixLength P v) :
    HEq (PaddedIntegralRowBits.polynomial (source P D H) (fun key=>P.cap (pairFst key)+1) u)
      (PaddedIntegralRowBits.polynomial (source P D H) (fun key=>P.cap (pairFst key)+1) v) := by
  exact ((source P D H).cell_row (fun key=>P.cap (pairFst key)+1) u).trans
    ((row_cell_congr _ _ _ _ (source_cell_congr P D H u v hr hb) (congrArg (fun r=>P.cap r+1) hr)).trans
      ((source P D H).cell_row (fun key=>P.cap (pairFst key)+1) v).symm)

end LeanCanny.Algebra.IntegralMixedFramedCompanionBits
