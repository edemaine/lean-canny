/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliarySlackMatrices
public import LeanCanny.Algebra.IntegralMixedFramedSlackRootProperties
/-! # Original-only integer sources for actual auxiliary marked slacks

All coefficients, degree bounds and mass ceilings are derived from the same
old candidate plan. The original radius is a native function, not advice.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliarySlackSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryPreparedRoot (dimension term dimension_unary term_FP)
open IntegralMixedAuxiliaryRecipeRoot (planAt dataAt)
open IntegralMixedAuxiliarySlackMatrix (parameters count charge radius degree regularization penalty)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def syntaxInput {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :=
  IntegralMixedAuxiliaryCandidateCoordinate.inputSyntax hn ht ha

theorem inputs {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    IntegralMixedFramedStepHeight.FamilyInputs (parameters n t) (planAt hn ht ha)
      (syntaxInput hn ht ha).nodes (syntaxInput hn ht ha).factor (syntaxInput hn ht ha).seed :=
  IntegralMixedAuxiliaryEmptyPlan.familyInputs (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))

noncomputable def sphereSource {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :=
  IntegralMixedFramedSlackRootBits.sphereSource (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)
    (syntaxInput hn ht ha) (inputs hn ht ha) (count n) (radius hn ht ha)
noncomputable def regularSource {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :=
  IntegralMixedFramedSlackRootBits.regularSource (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)
    (syntaxInput hn ht ha) (inputs hn ht ha) (count n) (degree t) (radius hn ht ha) (regularization hn ht ha) (penalty hn ht ha)

theorem sphere_access {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : IntegerPolynomialRootQueriesBits.Access (sphereSource hn ht ha) :=
  IntegralMixedFramedSlackRootBits.sphereAccess (parameters n t)
    (IntegralMixedAuxiliaryParameters.access (dimension_unary hn) (term_FP ht)) (planAt hn ht ha) (dataAt hn ht ha)
    (syntaxInput hn ht ha) (inputs hn ht ha)
    (fun root=>(IntegralMixedAuxiliaryEmptyPlan.description (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))).factor_positive root)
    (fun _=>by change 1≤1; exact le_rfl) (IntegralMixedAuxiliarySlackMatrix.count_unary hn) (IntegralMixedAuxiliarySlackMatrix.radius_binary hn ht ha)

theorem regular_access {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : IntegerPolynomialRootQueriesBits.Access (regularSource hn ht ha) :=
  IntegralMixedFramedSlackRootBits.regularAccess (parameters n t)
    (IntegralMixedAuxiliaryParameters.access (dimension_unary hn) (term_FP ht)) (planAt hn ht ha) (dataAt hn ht ha)
    (syntaxInput hn ht ha) (inputs hn ht ha)
    (fun root=>(IntegralMixedAuxiliaryEmptyPlan.description (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))).factor_positive root)
    (fun _=>by change 1≤1; exact le_rfl) (IntegralMixedAuxiliarySlackMatrix.count_unary hn) (IntegralMixedAuxiliarySlackMatrix.degree_binary ht)
    (IntegralMixedAuxiliarySlackMatrix.radius_binary hn ht ha) (IntegralMixedAuxiliarySlackMatrix.regularization_binary hn ht ha)
    (IntegralMixedAuxiliarySlackMatrix.penalty_binary hn ht ha)
    (fun key=>Nat.zero_lt_of_lt (LeanCanny.Geometry.BoundedRegularSource.powerDegree_gt_one (charge t key)))

theorem sphere_nonzero {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (key : List Bool) :
    (sphereSource hn ht ha).polynomial key≠0 :=
  IntegralMixedFramedSlackRootBits.sphere_nonzero (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)
    (syntaxInput hn ht ha) (inputs hn ht ha) (count n) (radius hn ht ha) key

theorem regular_nonzero {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (key : List Bool) :
    (regularSource hn ht ha).polynomial key≠0 :=
  IntegralMixedFramedSlackRootBits.regular_nonzero (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)
    (syntaxInput hn ht ha) (inputs hn ht ha) (count n) (degree t) (radius hn ht ha) (regularization hn ht ha) (penalty hn ht ha) key
    (Nat.zero_lt_of_lt (LeanCanny.Geometry.BoundedRegularSource.powerDegree_gt_one (charge t key)))

end LeanCanny.Encoding.IntegralMixedAuxiliarySlackSource
