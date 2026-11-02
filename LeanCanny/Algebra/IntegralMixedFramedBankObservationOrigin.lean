/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
/-! # Bundled actual bank data at chronological saved origins

The horizon, width, count and literal integer denominators move together.
No dependent coordinate transport or comparison of spatial sources is used.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankObservation
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family keyAt prefixLength)

 theorem data_at_word (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    ofState ((family P D H).state key)=atRun P D (pairFst key) (prefixLength P key) (min_le_right _ _) := rfl

theorem data_at_key (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (root : List Bool) (birth : ℕ) (tail : List Bool) (hb : birth≤P.cap root+1) :
    ofState ((family P D H).state (keyAt root birth tail))=atRun P D root birth hb :=
  (data_at_word P D H _).trans (atRun_congr P D _ root _ birth
    (IntegralMixedFramedHistoryFamilyBits.keyAt_root root birth tail)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root birth tail hb) _ hb)

theorem data_at_saved (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hb : birth P q≤P.cap (RankedHistoryTask.root q)+1) :
    ofState ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q))=atRun P D (RankedHistoryTask.root q) (birth P q) hb :=
  (data_at_word P D H _).trans (atRun_congr P D _ _ _ _
    (IntegralMixedFullHistoryFamilyBits.saved_root P q) (IntegralMixedFullHistoryFamilyBits.saved_prefix P q) _ hb)

theorem data_sibling (P : Parameters) (D : Plan P)
    (H K : IntegralMixedFramedHistoryFamilyBits.Data P D) (u v : List Bool)
    (hr : pairFst u=pairFst v) (hb : prefixLength P u=prefixLength P v) :
    ofState ((family P D H).state u)=ofState ((family P D K).state v) :=
  (data_at_word P D H u).trans ((atRun_congr P D _ _ _ _ hr hb _ _).trans (data_at_word P D K v).symm)

theorem point_at_key (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (root : List Bool) (birth : ℕ) (tail : List Bool) (hb : birth≤P.cap root+1) (z : ℕ→ℝ) (i : ℕ) :
    (ofState ((family P D H).state (keyAt root birth tail))).point z i=(atRun P D root birth hb).point z i :=
  congrArg (fun d : Data=>d.point z i) (data_at_key P D H root birth tail hb)

theorem point_sibling (P : Parameters) (D : Plan P)
    (H K : IntegralMixedFramedHistoryFamilyBits.Data P D) (u v : List Bool)
    (hr : pairFst u=pairFst v) (hb : prefixLength P u=prefixLength P v) (z : ℕ→ℝ) (i : ℕ) :
    (ofState ((family P D H).state u)).point z i=(ofState ((family P D K).state v)).point z i :=
  congrArg (fun d : Data=>d.point z i) (data_sibling P D H K u v hr hb)

end LeanCanny.Algebra.IntegralMixedFramedBankObservation
