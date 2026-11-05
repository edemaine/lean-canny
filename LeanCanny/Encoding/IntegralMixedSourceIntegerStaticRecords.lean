/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
public import LeanCanny.Algebra.IntegralMixedStaticRecordContinuation
/-! # Constant-source integer frontends use the literal static record compiler -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (Q : (r : List Bool)→SpatialSource (P.ambient r))
  (hn : ∀r,0<P.ambient r) (hdegree : ∀r,(Q r).degree=P.degree r)
  (hcap : ∀r,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient r+1) (P.degree r)≤2^P.width r)
  (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀r i,T.degree (pair r (BinaryNatCode.encode i))≤2^P.width r)
  (hroom : ∀r,IntegralMixedCausalRecordPlanBits.count r+N r+2≤P.cap r+1)

noncomputable def staticRecords (r : List Bool) := IntegralMixedStaticRecordPrefix.records (Q r) (hn r)
  (by rw [hdegree]; exact hcap r) (N r) (IntegralMixedCausalRecordPlanBits.count r)
  (fun i=>T.polynomial (pair r (BinaryNatCode.encode i))) (fun _=>hz _)
  (fun i=>(T.degree_bound _).trans (hT r i)) (IntegralMixedCausalRecordPlanBits.code r)

theorem staticRecords_length (r : List Bool) :
    (staticRecords P Q hn hdegree hcap N T hz hT r).length=IntegralMixedCausalRecordPlanBits.count r+N r :=
  IntegralMixedStaticRecordPrefix.records_length _ _ _ _ _ _ _ _ _

theorem rules_static (r : List Bool) :
    ((plan P (fun r _=>Q r) hn (fun r _=>hdegree r) hcap N T hz hT hroom).rules r)=
      IntegralMixedCausalPlanBits.commands
        (initial P (plan P (fun r _=>Q r) hn (fun r _=>hdegree r) hcap N T hz hT hroom) r)
        (staticRecords P Q hn hdegree hcap N T hz hT r)
        (by rw [staticRecords_length];have H := hroom r;omega) := by
  rfl

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
