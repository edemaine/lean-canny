/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalPrefixes
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
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native represents)
open IntegralMixedPhysicalCriticalPrefixes (birth key key_birth positive input)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

def saved (n : List Bool→ℕ) (outer : Bool) (p : List Bool) :=
  pair (key n outer false (pairFst p)) (pairSnd p)
include hn in
theorem saved_FP : saved n outer∈FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP (IntegralMixedPhysicalCriticalPrefixes.key_FP hn outer false)) pairSnd_mem_FP

noncomputable def originalSource :=IntegralMixedFramedCoordinateCharacteristicBits.rootSource
  (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
  (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed
  (bank hn ht ha hR outer).bounds

theorem originalAccess : IntegerPolynomialRootQueriesBits.Access (originalSource hn ht ha hR outer) := by
  cases outer
  · exact IntegralMixedFramedCoordinateCharacteristicBits.currentQ_rootAccess
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedAccess hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.callerControls hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.callerBounds hn ht ha hR) _ _ _
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha hR)
      (BinaryFn.const 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor_binary hn ht ha)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.seed_binary hn ht ha hR)
  · exact IntegralMixedFramedCoordinateCharacteristicBits.currentQ_rootAccess
      (IntegralMixedAuxiliaryOuterRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryOuterRecordPlan.certifiedAccess hn ht ha hR)
      (IntegralMixedAuxiliaryOuterRecordPlan.certifiedPlan hn ht ha hR)
      (IntegralMixedAuxiliaryOuterRecordPlan.certifiedData hn ht ha hR)
      (IntegralMixedAuxiliaryOuterRecordPlan.callerControls hn ht ha hR)
      (IntegralMixedAuxiliaryOuterRecordPlan.callerBounds hn ht ha hR) _ _ _
      (IntegralMixedAuxiliaryOuterRecordPlan.certifiedInputs hn ht ha hR)
      (BinaryFn.const 3) (IntegralMixedAuxiliaryOuterRecordPlan.factor_binary hn ht ha)
      (IntegralMixedAuxiliaryOuterRecordPlan.seed_binary hn ht ha hR)

noncomputable def source :=IntegerPolynomialSourceChoice.reindex (originalSource hn ht ha hR outer) (saved n outer)
theorem source_access : IntegerPolynomialRootQueriesBits.Access (source hn ht ha hR outer) :=
  IntegerPolynomialSourceChoice.reindex_access _ (originalAccess hn ht ha hR outer) (saved_FP hn outer)

def regroup (p : List Bool) := pair (pair (pairFst p) (pairFst (pairSnd p))) (pairSnd (pairSnd p))
theorem regroup_FP : regroup∈FP :=by polytime [regroup]
noncomputable def derivatives :=IntegerPolynomialSourceChoice.reindex
  (IntegerPolynomialIteratedDerivativeBits.source (source hn ht ha hR outer)) regroup
theorem derivatives_access : IntegerPolynomialRootQueriesBits.Access (derivatives hn ht ha hR outer) :=
  IntegerPolynomialSourceChoice.reindex_access _
    (IntegerPolynomialIteratedDerivativeBits.access (source_access hn ht ha hR outer)) regroup_FP

def selected (n : List Bool→ℕ) (outer child : Bool) (z : List Bool) :=
  min (Nat.fromBitsLE (pairFst (pairSnd z))) (birth n outer false (pairFst z)-1)+(if child then 1 else 0)
include hn in
theorem selected_unary (child : Bool) : UnaryFn (selected n outer child) :=
  (UnaryFn.fromBitsLE_min (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
    (((IntegralMixedPhysicalCriticalPrefixes.birth_unary hn outer false).comp pairFst_mem_FP).sub (UnaryFn.const 1))).add
      (UnaryFn.const (if child then 1 else 0))

noncomputable def coordinate (child : Bool) (q d : List Bool) : Fin
    ((family (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
      (bank hn ht ha hR outer).data).birth (key n outer child q)) :=
  ⟨selected n outer child (pair q d),by
    rw [key_birth hn ht ha hR outer]
    have HP:=IntegralMixedPhysicalCriticalPrefixes.birth_pos n outer false q
    have HC:=IntegralMixedPhysicalCriticalPrefixes.consecutive n outer q
    have HM:=min_le_right (Nat.fromBitsLE (pairFst d)) (birth n outer false q-1)
    cases child
    · simp only [selected,pairFst_pair,pairSnd_pair,Bool.false_eq_true,ite_false,Nat.add_zero]
      omega
    · simp only [selected,pairFst_pair,pairSnd_pair,ite_true]
      omega⟩

noncomputable def value (child : Bool) :=IntegralFramedPhysicalUnivariateTest.value
  (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
  (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed
  (bank hn ht ha hR outer).bounds (key n outer child) (positive hn ht ha hR outer child)
  (coordinate hn ht ha hR outer child) (derivatives hn ht ha hR outer)

attribute [local irreducible] bank native coordinate source derivatives originalSource

theorem evaluator (child : Bool) : SpaceFunction (value hn ht ha hR outer child) :=by
  let B:=bank hn ht ha hR outer
  let A:=native hn ht ha hR outer
  have HI : UnaryFn (IntegralFramedPhysicalUnivariateTest.selected B.parameters B.plan B.data
      (key n outer child) (coordinate hn ht ha hR outer child)) :=
    (selected_unary hn outer child).of_eq (fun z=>by
      simp only [IntegralFramedPhysicalUnivariateTest.selected,coordinate,selected,pairFst_pair,pairSnd_pair])
  exact IntegralFramedPhysicalUnivariateTest.evaluator B.parameters A.parameters B.plan B.data
    (tables hn ht ha hR outer) (tables_native hn ht ha hR outer) (represents hn ht ha hR outer)
    (key n outer child) (IntegralMixedPhysicalCriticalPrefixes.key_FP hn outer child)
    (coordinate hn ht ha hR outer child) HI
    A.liftedData A.controls A.bounds A.nodes A.factor A.seed B.bounds _ (derivatives_access hn ht ha hR outer)
    (positive hn ht ha hR outer child) (IntegralMixedPhysicalCriticalPrefixes.row_evaluator hn ht ha hR outer child)

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

noncomputable def degree (p : List Bool) :=(source hn ht ha hR outer).degree
  (pair (pairFst (pairFst p)) (BinaryNatCode.encode (pairSnd p).length))
theorem degree_binary : BinaryFn (degree hn ht ha hR outer) :=
  (source_access hn ht ha hR outer).degree.comp (mem_FP_pair
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP)

noncomputable def agrees (z : List Bool) : Prop :=
  ∀ i<birth n outer false (pairFst z),∀ k<degree hn ht ha hR outer (pair z (List.replicate i true))+1,
    value hn ht ha hR outer false (probe false (pair (pair z (List.replicate i true)) (BinaryNatCode.encode k)))=
      value hn ht ha hR outer true (probe true (pair (pair z (List.replicate i true)) (BinaryNatCode.encode k)))

theorem scanEvaluator : SpaceFunction (fun z=>[decide (agrees hn ht ha hR outer z)]) :=by
  have L:=(evaluator hn ht ha hR outer false).precompose (probe false) (probe_FP false)
  have C:=(evaluator hn ht ha hR outer true).precompose (probe true) (probe_FP true)
  have E:=(L.pairOutputs C).postcompose (fun z=>[decide (pairFst z=pairSnd z)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have D:=E.forall_binary ((degree_binary hn ht ha hR outer).add (BinaryFn.const 1))
  exact (D.forall_unary ((IntegralMixedPhysicalCriticalPrefixes.birth_unary hn outer false).comp pairFst_mem_FP)).congr
    (funext fun z=>by
      apply congrArg List.singleton
      apply Bool.eq_iff_iff.mpr
      simp only [agrees,Function.comp_apply,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq])

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankEquality
