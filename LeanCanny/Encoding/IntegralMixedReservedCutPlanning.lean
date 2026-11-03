/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordReadback
public import LeanCanny.Algebra.IntegralMixedFramedNormalizationPlanning
/-! # Certified planning preserves the literal original-source record compiler

The target parameters are chosen before words. Height/modulus planning does
not change source, width, cap, command bytes or current-Q instantiation.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedReservedCutPlanning
open LeanCanny.Algebra IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedHistoryScript
open IntegralMixedFramedNormalizationBits (planned plannedPlan plannedData)
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
 (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
 (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
 (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
 (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
 (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
 (L F C : List Bool→ℕ)

theorem plan_eq : plannedPlan P (IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom) L F C=
    IntegralMixedSourceIntegerRecordAppend.plan (planned P L F C) S hn hd hcap N T hz hT hroom:=rfl

theorem rules_eq (root : List Bool) :
    ((plannedPlan P (IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom) L F C).rules root)=
      (IntegralMixedSourceIntegerRecordAppend.plan (planned P L F C) S hn hd hcap N T hz hT hroom).rules root:=rfl

end LeanCanny.Encoding.IntegralMixedReservedCutPlanning
