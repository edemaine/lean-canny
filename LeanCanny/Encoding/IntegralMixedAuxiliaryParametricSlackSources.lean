/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliarySlackSources
public import LeanCanny.Algebra.IntegralMixedFramedSlackRootProperties
/-! # Original-only integer sources for actual auxiliary marked slacks

The outer radius is an independent native binary field on the full saved key.
The old algebra and both polynomial degrees remain independent of that radius.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryParametricSlackSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryPreparedRoot (dimension term dimension_unary term_FP)
open IntegralMixedAuxiliaryRecipeRoot (planAt dataAt)
open IntegralMixedAuxiliarySlackMatrix (parameters count charge radius degree regularization penalty)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

open IntegralMixedAuxiliarySlackSource (syntaxInput inputs)

def regularizationAt (n : List Bool → ℕ) (t : List Bool → Term)
    (R : List Bool → ℕ) (key : List Bool) :=
  LeanCanny.Geometry.BoundedRegularSource.regularizationExponent
    (count n key) (charge t key) (charge t key) (R key)
def penaltyAt (n : List Bool → ℕ) (t : List Bool → Term)
    (R : List Bool → ℕ) (key : List Bool) :=
  LeanCanny.Geometry.BoundedZeroSource.penaltyExponent (count n key) (charge t key) (R key)

theorem regularizationAt_binary {n : List Bool → ℕ} {t : List Bool → Term} {R : List Bool → ℕ}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (hR : BinaryFn R) :
    BinaryFn (regularizationAt n t R) :=
  BoundedRegularControls.regularizationExponent_binary (IntegralMixedAuxiliarySlackMatrix.count_unary hn)
    (BinaryFn.ofUnary (IntegralMixedAuxiliarySlackMatrix.charge_unary ht))
    (BinaryFn.ofUnary (IntegralMixedAuxiliarySlackMatrix.charge_unary ht)) hR

theorem penaltyAt_binary {n : List Bool → ℕ} {t : List Bool → Term} {R : List Bool → ℕ}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (hR : BinaryFn R) :
    BinaryFn (penaltyAt n t R) :=
  (hR.mul (IntegralMixedAuxiliarySlackMatrix.degree_binary ht)).add
    (BinaryFn.ofUnary ((IntegralMixedAuxiliarySlackMatrix.count_unary hn).add (UnaryFn.const 2))).size

noncomputable def sphereSource {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (R : List Bool → ℕ) :=
  IntegralMixedFramedSlackRootBits.sphereSource (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)
    (syntaxInput hn ht ha) (inputs hn ht ha) (count n) R
noncomputable def regularSource {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (R : List Bool → ℕ) :=
  IntegralMixedFramedSlackRootBits.regularSource (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)
    (syntaxInput hn ht ha) (inputs hn ht ha) (count n) (degree t) R (regularizationAt n t R) (penaltyAt n t R)

theorem sphere_access {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) {R : List Bool → ℕ} (hR : BinaryFn R) : IntegerPolynomialRootQueriesBits.Access (sphereSource hn ht ha R) :=
  IntegralMixedFramedSlackRootBits.sphereAccess (parameters n t)
    (IntegralMixedAuxiliaryParameters.access (dimension_unary hn) (term_FP ht)) (planAt hn ht ha) (dataAt hn ht ha)
    (syntaxInput hn ht ha) (inputs hn ht ha)
    (fun root=>(IntegralMixedAuxiliaryEmptyPlan.description (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))).factor_positive root)
    (fun _=>by change 1≤1; exact le_rfl) (IntegralMixedAuxiliarySlackMatrix.count_unary hn) hR

theorem regular_access {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) {R : List Bool → ℕ} (hR : BinaryFn R) : IntegerPolynomialRootQueriesBits.Access (regularSource hn ht ha R) :=
  IntegralMixedFramedSlackRootBits.regularAccess (parameters n t)
    (IntegralMixedAuxiliaryParameters.access (dimension_unary hn) (term_FP ht)) (planAt hn ht ha) (dataAt hn ht ha)
    (syntaxInput hn ht ha) (inputs hn ht ha)
    (fun root=>(IntegralMixedAuxiliaryEmptyPlan.description (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))).factor_positive root)
    (fun _=>by change 1≤1; exact le_rfl) (IntegralMixedAuxiliarySlackMatrix.count_unary hn) (IntegralMixedAuxiliarySlackMatrix.degree_binary ht)
    hR (regularizationAt_binary hn ht hR)
    (penaltyAt_binary hn ht hR)
    (fun key=>Nat.zero_lt_of_lt (LeanCanny.Geometry.BoundedRegularSource.powerDegree_gt_one (charge t key)))

theorem sphere_nonzero {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (R : List Bool → ℕ) (key : List Bool) :
    (sphereSource hn ht ha R).polynomial key≠0 :=
  IntegralMixedFramedSlackRootBits.sphere_nonzero (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)
    (syntaxInput hn ht ha) (inputs hn ht ha) (count n) R key

theorem regular_nonzero {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (R : List Bool → ℕ) (key : List Bool) :
    (regularSource hn ht ha R).polynomial key≠0 :=
  IntegralMixedFramedSlackRootBits.regular_nonzero (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)
    (syntaxInput hn ht ha) (inputs hn ht ha) (count n) (degree t) R (regularizationAt n t R) (penaltyAt n t R) key
    (Nat.zero_lt_of_lt (LeanCanny.Geometry.BoundedRegularSource.powerDegree_gt_one (charge t key)))

end LeanCanny.Encoding.IntegralMixedAuxiliaryParametricSlackSource
