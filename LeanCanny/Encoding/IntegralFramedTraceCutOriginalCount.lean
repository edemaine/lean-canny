/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTraceCutSource
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
/-! # Count shields for original record scripts and their fixed terminal sampler -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
open LeanCanny.Algebra IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)

theorem script_length (root : List Bool) :
    ((plan P S hn hd hcap N T hz hT hroom).rules root).length=IntegralMixedCausalRecordPlanBits.count root+N root := by
  unfold plan
  rw [IntegralMixedSourceIntegerPrelude.extended_length,later_length]
end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend

namespace LeanCanny.Encoding.IntegralFramedTraceCutSource
open LeanCanny.Algebra IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
set_option backward.isDefEq.respectTransparency false

theorem input_count (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (root : List Bool) :
    (input P D H L F C hs).count root=IntegralFramedTraceCutMetadata.length P D root+1 :=
  IntegralFramedTraceCutMetadata.terminal_birth P D H root
end LeanCanny.Encoding.IntegralFramedTraceCutSource
