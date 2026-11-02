/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyBankTermTest
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateTermPoint
/-! # An original-only polynomial test on the actual candidate sampler -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters
noncomputable def termSampleInput {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (key : List Bool→List Bool)
    (hpos : ∀ c,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key c)) : SquareSampleInput.Inputs :=
  IntegralFramedBankTermTest.input (parameters n t) (plan hn ht ha) (data hn ht ha) (termSyntax hn ht ha)
    (familyInputs hn ht ha) key
    (fun c=>(hpos c).trans_eq (IntegralMixedFramedHistoryFamilyBits.family_birth (parameters n t)
      (plan hn ht ha) (data hn ht ha) (key c)).symm)
theorem termSampleInput_eq {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (key : List Bool→List Bool)
    (hpos : ∀ c,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key c)) :
    termSampleInput hn ht ha key hpos=squareInput hn ht ha key hpos := rfl
end LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan

namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliaryRecipeRoot
open IntegralMixedAuxiliaryPreparedRoot (dimension term dimension_unary term_FP)
open scoped Classical
attribute [local irreducible] parameters scalarWidth scalarCeiling spatialDegree degreeCharge augmented

noncomputable def termInput {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :=
  IntegralMixedAuxiliaryEmptyPlan.termSampleInput (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))
    (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id)
    (IntegralMixedAuxiliaryPositivePrefix.key_positive (dimension n) (term t) id)

theorem termInput_eq {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    termInput hn ht ha=input hn ht ha :=
  IntegralMixedAuxiliaryEmptyPlan.termSampleInput_eq _ _ _ _ _

noncomputable def termValue {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :=
  IntegralMixedAuxiliaryEmptyPlan.termValue (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))
    (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id)
    (IntegralMixedAuxiliaryPositivePrefix.key_positive (dimension n) (term t) id)
    (fun root=>(t (pairFst root)).toData.toBits)

theorem termValue_space {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    SpaceFunction (termValue hn ht ha) :=
  IntegralMixedAuxiliaryEmptyPlan.term_evaluator (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))
    _ (IntegralMixedAuxiliaryPositivePrefix.key_FP (dimension_unary hn) id_mem_FP) _ _
    (mem_FP_comp pairFst_mem_FP ht)

noncomputable def termQuery {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (q : List Bool) :=
  pair (packet hn ht ha q) []

theorem termQuery_FP {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    termQuery hn ht ha∈FP := mem_FP_pair (packet_FP hn ht ha) (constFn_mem_FP [])

end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
