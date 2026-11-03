/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardBounds
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalAncestry
/-! # The physical guard column belongs to the actual creating critical block -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCriticalGuardBits
open LeanCanny.Encoding IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedHeaderTablesBits (Tables)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (T : Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
  (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool)
include hr

theorem header_actual : header T key stage q=IntegralMixedCommandHeaderBits.command
    (IntegralMixedFramedRootPullback.instructionAt P D (pairFst (key q)) (stage q)).command := by
  unfold header
  rw [hr.commands,IntegralMixedFramedHeaderBits.lookup_words (D.rules (pairFst (key q)))
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst (key q))) (by rfl)]
  rfl

theorem active_critical (ha : Active P T key stage q) :
    ∃ r : CriticalRule (P.ambient (pairFst (key q))),
      (IntegralMixedFramedRootPullback.instructionAt P D (pairFst (key q)) (stage q)).command=.critical r := by
  have HC:=ha.2
  rw [header_actual P D H T hr key stage q] at HC
  cases hcmd:(IntegralMixedFramedRootPullback.instructionAt P D (pairFst (key q)) (stage q)).command with
  | integer=>rw [hcmd] at HC; cases HC
  | critical r=>exact ⟨r,rfl⟩
  | cut r k=>rw [hcmd] at HC; cases k <;> cases HC

theorem physical_at_critical (r : CriticalRule (P.ambient (pairFst (key q))))
    (hc : (IntegralMixedFramedRootPullback.instructionAt P D (pairFst (key q)) (stage q)).command=.critical r) :
    physical P T key stage q=
      IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryScript.paddedPast
        (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst (key q)))
        (D.rules (pairFst (key q))) (stage q))+r.offset.val+
          r.coordinate%(P.ambient (pairFst (key q))-r.offset.val+1) := by
  unfold physical packet
  rw [IntegralMixedFramedPhysicalIndex.prefixArity_packet P D H T hr,
    header_actual P D H T hr key stage q,hc]
  rfl
end LeanCanny.Algebra.IntegralMixedFramedCriticalGuardBits
