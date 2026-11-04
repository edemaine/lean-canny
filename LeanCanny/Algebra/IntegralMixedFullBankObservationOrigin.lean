/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullBankObservation
/-! # Same-root full bank observations depend on the actual prefix only -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullBankObservation
open LeanCanny.Encoding IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits

private theorem at_congr (P : Parameters) (D : Plan P) (r s : List Bool) (a b : ℕ)
    (hr : r=s) (hb : a=b) (ha : a≤P.cap r+1) (hc : b≤P.cap s+1) :
    atRun P D r a ha=atRun P D s b hc :=by
  subst s
  subst b
  rfl

theorem data_sibling (P : Parameters) (D : Plan P)
    (H J : IntegralMixedFramedHistoryFamilyBits.Data P D) (u v : List Bool)
    (hr : pairFst u=pairFst v) (hb : prefixLength P u=prefixLength P v) :
    atFamily P D H u=atFamily P D J v :=by
  change atRun P D (pairFst u) (prefixLength P u) (min_le_right _ _)=
    atRun P D (pairFst v) (prefixLength P v) (min_le_right _ _)
  exact at_congr P D _ _ _ _ hr hb _ _

theorem point_sibling (P : Parameters) (D : Plan P)
    (H J : IntegralMixedFramedHistoryFamilyBits.Data P D) (u v : List Bool)
    (hr : pairFst u=pairFst v) (hb : prefixLength P u=prefixLength P v) (z : ℕ→ℝ) (i : ℕ) :
    (atFamily P D H u).point z i=(atFamily P D J v).point z i :=
  congrArg (fun d : Data=>d.point z i) (data_sibling P D H J u v hr hb)

end LeanCanny.Algebra.IntegralMixedFullBankObservation
