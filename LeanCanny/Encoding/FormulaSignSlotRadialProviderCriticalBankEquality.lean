/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalPrefixes
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFieldEquality
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateCurrentQSpace
public import LeanCanny.Algebra.IntegerPolynomialIteratedDerivativeSource
public import LeanCanny.Algebra.IntegerPolynomialSourceChoice
public import LeanCanny.Encoding.IntegralFramedPhysicalUnivariateSpace
public import LeanCanny.Computation.SpaceFunctionBinaryQuantifiers
public import LeanCanny.Computation.SpaceFunctionQuantifiers
/-! # Every old quotient is compared at the same full parent and child words

The parent common-cleared coordinate characteristic polynomial is evaluated
at both quotients. All derivative signs are streamed, with no selected-root
regularity hypothesis and no interpreted coordinate reader.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalBankEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderCriticalPrefixes (birth key key_birth positive input)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable def saved (p : List Bool) :=
  pair (key false (pairFst p)) (pairSnd p)
theorem saved_FP : saved∈FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP (FormulaSignSlotRadialProviderCriticalPrefixes.key_FP false)) pairSnd_mem_FP

noncomputable def originalSource := FormulaSignSlotRadialProviderFieldEquality.originalSource
theorem originalAccess : IntegerPolynomialRootQueriesBits.Access originalSource :=
  FormulaSignSlotRadialProviderFieldEquality.originalAccess

noncomputable def source :=IntegerPolynomialSourceChoice.reindex (originalSource) (saved)
theorem source_access : IntegerPolynomialRootQueriesBits.Access (source) :=
  IntegerPolynomialSourceChoice.reindex_access _ (originalAccess) saved_FP

def regroup (p : List Bool) := pair (pair (pairFst p) (pairFst (pairSnd p))) (pairSnd (pairSnd p))
theorem regroup_FP : regroup∈FP :=by polytime [regroup]
noncomputable def derivatives :=IntegerPolynomialSourceChoice.reindex
  (IntegerPolynomialIteratedDerivativeBits.source (source)) regroup
theorem derivatives_access : IntegerPolynomialRootQueriesBits.Access (derivatives) :=
  IntegerPolynomialSourceChoice.reindex_access _
    (IntegerPolynomialIteratedDerivativeBits.access (source_access)) regroup_FP

noncomputable def selected (child : Bool) (z : List Bool) :=
  min (Nat.fromBitsLE (pairFst (pairSnd z))) (birth false (pairFst z)-1)+(if child then 1 else 0)
theorem selected_unary (child : Bool) : UnaryFn (selected child) :=
  (UnaryFn.fromBitsLE_min (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
    (((FormulaSignSlotRadialProviderCriticalPrefixes.birth_unary false).comp pairFst_mem_FP).sub (UnaryFn.const 1))).add
      (UnaryFn.const (if child then 1 else 0))

noncomputable def coordinate (child : Bool) (q d : List Bool) : Fin
    ((family (FormulaSignSlotRadialProviderRecordPlan.bank).parameters (FormulaSignSlotRadialProviderRecordPlan.bank).plan
      (FormulaSignSlotRadialProviderRecordPlan.bank).data).birth (key child q)) :=
  ⟨selected child (pair q d),by
    rw [key_birth]
    have HP:=FormulaSignSlotRadialProviderCriticalPrefixes.birth_pos false q
    have HC:=FormulaSignSlotRadialProviderCriticalPrefixes.consecutive q
    have HM:=min_le_right (Nat.fromBitsLE (pairFst d)) (birth false q-1)
    cases child
    · simp only [selected,pairFst_pair,pairSnd_pair,Bool.false_eq_true,ite_false,Nat.add_zero]
      omega
    · simp only [selected,pairFst_pair,pairSnd_pair,ite_true]
      omega⟩

noncomputable def value (child : Bool) :=IntegralFramedPhysicalUnivariateTest.value
  (FormulaSignSlotRadialProviderRecordPlan.bank).parameters (FormulaSignSlotRadialProviderRecordPlan.bank).plan (FormulaSignSlotRadialProviderRecordPlan.bank).data
  (FormulaSignSlotRadialProviderRecordPlan.bank).nodes (FormulaSignSlotRadialProviderRecordPlan.bank).factor (FormulaSignSlotRadialProviderRecordPlan.bank).seed
  (FormulaSignSlotRadialProviderRecordPlan.bank).bounds (key child) (positive child)
  (coordinate child) (derivatives)

attribute [local irreducible] coordinate source derivatives originalSource

theorem evaluator (child : Bool) : SpaceFunction (value child) :=by
  let B:=FormulaSignSlotRadialProviderRecordPlan.bank
  let A:=FormulaSignSlotRadialProviderRecordPlan.bank_access
  have HI : UnaryFn (IntegralFramedPhysicalUnivariateTest.selected B.parameters B.plan B.data
      (key child) (coordinate child)) :=
    (selected_unary child).of_eq (fun z=>by
      simp only [IntegralFramedPhysicalUnivariateTest.selected,coordinate,selected,pairFst_pair,pairSnd_pair])
  exact IntegralFramedPhysicalUnivariateTest.evaluator B.parameters A.parameters B.plan B.data
    (FormulaSignSlotRadialProviderRecordPlan.tables) (FormulaSignSlotRadialProviderRecordPlan.tables_native) (FormulaSignSlotRadialProviderAtomic.bank_represents)
    (key child) (FormulaSignSlotRadialProviderCriticalPrefixes.key_FP child)
    (coordinate child) HI
    A.liftedData A.controls A.bounds A.nodes A.factor A.seed B.bounds _ (derivatives_access)
    (positive child) (FormulaSignSlotRadialProviderCriticalPrefixes.row_evaluator child)

/-- The outer finite-word packet pairs the fixed query with one child word. -/
def probe (child : Bool) (p : List Bool) :=
  let z:=pairFst (pairFst p)
  let q:=pairFst z
  pair (pair q (if child then pairSnd z else IntegralMixedPhysicalCriticalQuery.parentWord q))
    (pair (BinaryNatCode.encode (pairSnd (pairFst p)).length) (pairSnd p))
theorem probe_FP (child : Bool) : probe child∈FP := by
  have HZ :=mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HQ :=mem_FP_comp HZ pairFst_mem_FP
  have HP : IntegralMixedPhysicalCriticalQuery.parentWord∈FP :=mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have HW : (fun p=>if child then pairSnd (pairFst (pairFst p)) else
      IntegralMixedPhysicalCriticalQuery.parentWord (pairFst (pairFst (pairFst p))))∈FP :=by
    cases child
    · simpa only [Bool.false_eq_true,ite_false,Function.comp_def] using mem_FP_comp HQ HP
    · simpa only [ite_true,Function.comp_def] using mem_FP_comp HZ pairSnd_mem_FP
  have HI : UnaryFn (fun p : List Bool=>(pairSnd (pairFst p)).length) :=
    UnaryFn.length (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  exact mem_FP_pair (mem_FP_pair HQ HW) (mem_FP_pair (BinaryFn.ofUnary HI).bits_mem_FP pairSnd_mem_FP)

noncomputable def degree (p : List Bool) :=(source).degree
  (pair (pairFst (pairFst p)) (BinaryNatCode.encode (pairSnd p).length))
theorem degree_binary : BinaryFn (degree) :=
  (source_access).degree.comp (mem_FP_pair
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP)

noncomputable def agrees (z : List Bool) : Prop :=
  ∀ i<birth false (pairFst z),∀ k<degree (pair z (List.replicate i true))+1,
    value false (probe false (pair (pair z (List.replicate i true)) (BinaryNatCode.encode k)))=
      value true (probe true (pair (pair z (List.replicate i true)) (BinaryNatCode.encode k)))

theorem scanEvaluator : SpaceFunction (fun z=>[decide (agrees z)]) :=by
  have L:=(evaluator false).precompose (probe false) (probe_FP false)
  have C:=(evaluator true).precompose (probe true) (probe_FP true)
  have E:=(L.pairOutputs C).postcompose (fun z=>[decide (pairFst z=pairSnd z)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have D:=E.forall_binary ((degree_binary).add (BinaryFn.const 1))
  exact (D.forall_unary ((FormulaSignSlotRadialProviderCriticalPrefixes.birth_unary false).comp pairFst_mem_FP)).congr
    (funext fun z=>by
      apply congrArg List.singleton
      apply Bool.eq_iff_iff.mpr
      simp only [agrees,Function.comp_apply,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq])

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalBankEquality
