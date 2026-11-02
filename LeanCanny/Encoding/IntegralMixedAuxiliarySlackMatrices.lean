/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedSlackMatrixSpace
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateCoordinateSource
public import LeanCanny.Geometry.AuxiliaryCandidateRegularLift
public import LeanCanny.Encoding.BoundedRegularControls
/-! # Actual auxiliary banks have original-only marked-slack matrix readers

Every numeric control is derived from the original dimension/term and the
already certified candidate radius. No saved source width, height, matrix,
leading or common-denominator reader is supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliarySlackMatrix
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR LeanCanny.Geometry
open IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryPreparedRoot (dimension term dimension_unary term_FP)
open IntegralMixedAuxiliaryRecipeRoot (planAt dataAt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def original (key : List Bool) := pairFst (pairFst key)
theorem original_FP : original∈FP := mem_FP_comp (f := pairFst) (g := pairFst) pairFst_mem_FP pairFst_mem_FP

def count (n : List Bool → ℕ) (key : List Bool) := n (original key)
def charge (t : List Bool → Term) (key : List Bool) := AuxiliaryCandidateRegularLift.allowance t (original key)
noncomputable def radius {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (key : List Bool) :=
  IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha (original key)
def degree (t : List Bool → Term) (key : List Bool) := BoundedZeroSource.powerDegree (charge t key)
noncomputable def regularization {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (key : List Bool) :=
  BoundedRegularSource.regularizationExponent (count n key) (charge t key) (charge t key) (radius hn ht ha key)
noncomputable def penalty {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (key : List Bool) :=
  BoundedZeroSource.penaltyExponent (count n key) (charge t key) (radius hn ht ha key)

theorem count_unary {n : List Bool → ℕ} (hn : UnaryFn n) : UnaryFn (count n) := hn.comp original_FP
theorem charge_unary {t : List Bool → Term} (ht : (fun q=>(t q).toData.toBits)∈FP) : UnaryFn (charge t) :=
  (AuxiliaryCandidateRegularLift.allowance_unary ht).comp original_FP

theorem degree_binary {t : List Bool → Term} (ht : (fun q=>(t q).toData.toBits)∈FP) : BinaryFn (degree t) :=
  BoundedZeroControls.powerDegree_binary (BinaryFn.ofUnary (charge_unary ht))
theorem radius_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : BinaryFn (radius hn ht ha) :=
  (IntegralMixedAuxiliaryCandidateRadius.radius_binary hn ht ha).comp original_FP

theorem regularization_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : BinaryFn (regularization hn ht ha) :=
  BoundedRegularControls.regularizationExponent_binary (count_unary hn) (BinaryFn.ofUnary (charge_unary ht))
    (BinaryFn.ofUnary (charge_unary ht)) (radius_binary hn ht ha)
theorem penalty_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : BinaryFn (penalty hn ht ha) :=
  ((radius_binary hn ht ha).mul (degree_binary ht)).add (BinaryFn.ofUnary ((count_unary hn).add (UnaryFn.const 2))).size

noncomputable abbrev parameters (n : List Bool → ℕ) (t : List Bool → Term) := IntegralMixedAuxiliaryParameters.parameters (dimension n) (term t)

noncomputable def sphereValue {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :=
  IntegralMixedFramedSlackMatrixBits.sphereValue (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) (count n) (radius hn ht ha)
noncomputable def regularValue {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :=
  IntegralMixedFramedSlackMatrixBits.regularValue (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) (count n) (degree t)
    (radius hn ht ha) (regularization hn ht ha) (penalty hn ht ha)

theorem sphere_evaluator {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : SpaceFunction (sphereValue hn ht ha) :=
  IntegralMixedFramedSlackMatrixBits.sphere_evaluator (parameters n t)
    (IntegralMixedAuxiliaryParameters.access (dimension_unary hn) (term_FP ht)) (planAt hn ht ha) (dataAt hn ht ha)
    (IntegralMixedAuxiliaryCandidateCoordinate.inputSyntax hn ht ha)
    (IntegralMixedAuxiliaryEmptyPlan.familyInputs (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q)))
    (fun root=>(IntegralMixedAuxiliaryEmptyPlan.description (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))).factor_positive root)
    (fun _=>by change 1≤1; exact le_rfl) (count_unary hn) (radius_binary hn ht ha)

theorem regular_evaluator {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : SpaceFunction (regularValue hn ht ha) :=
  IntegralMixedFramedSlackMatrixBits.regular_evaluator (parameters n t)
    (IntegralMixedAuxiliaryParameters.access (dimension_unary hn) (term_FP ht)) (planAt hn ht ha) (dataAt hn ht ha)
    (IntegralMixedAuxiliaryCandidateCoordinate.inputSyntax hn ht ha)
    (IntegralMixedAuxiliaryEmptyPlan.familyInputs (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q)))
    (fun root=>(IntegralMixedAuxiliaryEmptyPlan.description (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))).factor_positive root)
    (fun _=>by change 1≤1; exact le_rfl) (count_unary hn) (degree_binary ht) (radius_binary hn ht ha)
    (regularization_binary hn ht ha) (penalty_binary hn ht ha)

end LeanCanny.Encoding.IntegralMixedAuxiliarySlackMatrix
