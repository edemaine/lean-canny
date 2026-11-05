/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedPlan
public import LeanCanny.Encoding.CoefficientMarkedRecordBankDenominator
/-! # Actual marked critical headers contain no radius-dependent coefficients -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordCriticalMetadata
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem headerTable_planned (P:Parameters) (L F C:List Bool→ℕ) (N:List Bool→ℕ) (ctx:List Bool):
    IntegralMixedSourceIntegerRecordAppend.headerTable (IntegralMixedFramedNormalizationBits.planned P L F C) N ctx=
      IntegralMixedSourceIntegerRecordAppend.headerTable P N ctx:=rfl

private theorem planned_tables
    (P:Parameters) (S:(root:List Bool)→ℕ→SpatialSource (P.ambient root))
    (hn0:∀root,0<P.ambient root) (hd:∀root b,(S root b).degree=P.degree root)
    (hcap:∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (N:List Bool→ℕ)
    (hq:∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (S root 0).degree≤2^P.width root)
    (T:IntegerPolynomialRootQueriesBits.Source) (hz:∀q,T.polynomial q≠0)
    (hT:∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (hroom:∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
    (hW:∀root,(P.degree root).size≤P.sourceWidth root)
    (a:Access P) (hN:UnaryFn N) (hA:IntegerPolynomialRootQueriesBits.Access T)
    (R:BoundedFullWriter.Readers) (hR:R.PolyTime)
    (scope:∀key,(LeanCanny.ETR.TermView.term (R.source key)).arity≤R.dim key)
    (s:BoundedRegularFramedOriginalBits.Snapshot P
      (IntegralMixedSourceIntegerRecordAppend.plan P S hn0 hd hcap N T hz hT hroom) R)
    (L F C:List Bool→ℕ) (hL:BinaryFn L) (hF:BinaryFn F) (hC:BinaryFn C):
    (IntegralMixedSourceIntegerRecordAppend.plannedControls P S hn0 hd hcap N hq T hz hT hroom hW
      a hN hA R hR scope s L F C hL hF hC).scalar.tables=
      IntegralMixedCausalPlanBits.tables P
        (IntegralMixedSourceIntegerRecordAppend.originalRecords P S hn0 hd hcap N hq T hz hT):=rfl

private theorem tables_ext (A B:IntegralMixedHeaderTablesBits.Tables)
    (hc:A.commands=B.commands) (hf:A.fallback=B.fallback):A=B:=by
  cases A
  cases B
  cases hc
  cases hf
  rfl

variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

noncomputable def tables:IntegralMixedHeaderTablesBits.Tables where
  commands:=IntegralMixedSourceIntegerRecordAppend.headerTable
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (fun ctx=>IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8)
  fallback:=IntegralMixedCausalPlanBits.fallbackWords (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)

noncomputable def runtimeTables (R:List Bool→ℕ):IntegralMixedHeaderTablesBits.Tables:=
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  IntegralMixedCausalPlanBits.tables P (IntegralMixedSourceIntegerRecordAppend.originalRecords P
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.spatial_cap hn ht ha)
    (fun root=>IntegralMixedAuxiliaryMarkedIntegerSource.number n root+8)
    (IntegralMixedAuxiliaryMarkedRecordPlan.source_cap hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R))

private theorem actual_tables {R:List Bool→ℕ} (hR:BinaryFn R):
    IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false=runtimeTables hn ht ha R:=by
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  have HC:=planned_tables P
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.spatial_cap hn ht ha)
    (fun root=>IntegralMixedAuxiliaryMarkedIntegerSource.number n root+8)
    (IntegralMixedAuxiliaryMarkedRecordPlan.source_cap hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R)
    (IntegralMixedAuxiliaryMarkedRecordPlan.room hn ht ha) (fun _=>le_rfl)
    (IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha)
    ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8))
    (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders n t R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.savedReaders_native hn ht hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.scope ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.snapshot hn ht ha R)
    (fun _=>3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) (BinaryFn.const 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor_binary hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed_binary hn ht ha hR)
  exact HC

theorem commands_eq {R:List Bool→ℕ} (hR:BinaryFn R) (ctx:List Bool):
    (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false).commands ctx=(tables hn ht ha).commands ctx:=by
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  have HE:=IntegralMixedSourceIntegerRecordAppend.headerWords_eq P
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.spatial_cap hn ht ha)
    (fun root=>IntegralMixedAuxiliaryMarkedIntegerSource.number n root+8)
    (IntegralMixedAuxiliaryMarkedRecordPlan.source_cap hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R) ctx
  have HC:=actual_tables hn ht ha hR
  exact (congrArg (fun T:IntegralMixedHeaderTablesBits.Tables=>T.commands ctx) HC).trans HE

theorem tables_eq {R:List Bool→ℕ} (hR:BinaryFn R):
    IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false=tables hn ht ha:=by
  have HC: (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false).commands=(tables hn ht ha).commands:=
    funext (commands_eq hn ht ha hR)
  have HRuntime:=congrArg IntegralMixedHeaderTablesBits.Tables.fallback (actual_tables hn ht ha hR)
  have HStatic:(runtimeTables hn ht ha R).fallback=(tables hn ht ha).fallback:=rfl
  have HF: (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false).fallback=(tables hn ht ha).fallback:=
    HRuntime.trans HStatic
  exact tables_ext _ _ HC HF

end LeanCanny.Encoding.CoefficientMarkedRecordCriticalMetadata
