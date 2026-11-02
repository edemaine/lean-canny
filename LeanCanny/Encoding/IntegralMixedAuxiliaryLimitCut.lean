/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryLimitRecords
/-! # Exact canonical-dilation command at the literal once-augmented source -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryLimitRecord
open LeanCanny.Algebra IntegralMixedHistory
open LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem cut_congr {N B : ℕ} (S : SpatialSource N) (r s : IntegralMixedCriticalSweep.Rule N)
    (hrs : r=s) (c d : ℕ)
    (ha : c<IntegralMixedLimitCoordinate.ChoiceBound S r) (hb : c<IntegralMixedLimitCoordinate.ChoiceBound S s)
    (hd : d≤IntegralMixedExceptionalBounds.auxiliaryCap (N+1) S.degree) (hB : d≤2^B) :
    (IntegralMixedFullHistoryScript.Command.cut r (.limitCoordinate ⟨0,Nat.succ_pos _⟩ ⟨c,ha⟩) d hd hB :
      IntegralMixedFullHistoryScript.Command S B) =
      .cut s (.limitCoordinate ⟨0,Nat.succ_pos _⟩ ⟨c,hb⟩) d hd hB := by
  cases hrs
  rfl

theorem cut_dilation {n B : ℕ} (S : SpatialSource (n+2)) (k m0 c d : ℕ) (hk : k≤n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) S.degree≤2^B)
    (hc : c<IntegralMixedLimitCoordinate.ChoiceBound S
      (IntegralMixedCanonicalDilation.rule (n:=n+1) (by omega : k≤n+1) (frontSelector k m0)))
    (hd : d≤IntegralMixedExceptionalBounds.auxiliaryCap (n+3) S.degree) :
    IntegralMixedCanonicalUnitRuleBits.command S (by omega) (m0+k) (record n k m0 c d) hcap =
      .cut (IntegralMixedCanonicalDilation.rule (n:=n+1) (by omega : k≤n+1) (frontSelector k m0))
        (.limitCoordinate ⟨0,Nat.succ_pos _⟩ ⟨c,hc⟩) d hd (hd.trans hcap) := by
  have hc' : c<IntegralMixedLimitCoordinate.ChoiceBound S
      (IntegralMixedCanonicalUnitRuleBits.virtual (n+2) (by omega) (m0+k) (record n k m0 c d)) := by
    rw [virtual_rule n k m0 c d hk]
    exact hc
  exact (cut_command S k m0 c d hcap hc' hd).trans
    (cut_congr S _ _ (virtual_rule n k m0 c d hk) c d hc' hc hd (hd.trans hcap))
end LeanCanny.Encoding.IntegralMixedAuxiliaryLimitRecord
