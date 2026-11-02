/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateRootSource
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidatePoint
/-! # Native integer coordinate sources for actual auxiliary candidates

A context pairs the complete original candidate packet with a retained index.
The source root uses only its advice block. The actual positive prefix, all
creator choices and the coefficient caller modulus are preserved.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateCoordinate
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedAuxiliaryParameters
open IntegralMixedAuxiliaryPreparedRoot (dimension term dimension_unary term_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def inputSyntax {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :=
  IntegralMixedEmptyTiltedNative.inputSyntax (parameters (dimension n) (term t))
    (access (dimension_unary hn) (term_FP ht))
    (IntegralMixedAuxiliaryEmptyPlan.description (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q)))
    (ambient_positive (dimension n) (term t)) (auxiliary_cap (dimension n) (term t))
    (room (dimension n) (term t)) (source_width (dimension n) (term t))

noncomputable def oldSource {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :=
  IntegralMixedFramedCoordinateCharacteristicBits.rootSource (parameters (dimension n) (term t))
    (IntegralMixedAuxiliaryRecipeRoot.planAt hn ht ha) (IntegralMixedAuxiliaryRecipeRoot.dataAt hn ht ha)
    (fun _=>1) (IntegralMixedAuxiliarySchedule.factor (dimension n) (term t))
    (IntegralMixedAuxiliarySchedule.seed (dimension n) (term t))
    (IntegralMixedAuxiliaryEmptyPlan.familyInputs (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q)))

theorem oldAccess {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    IntegerPolynomialRootQueriesBits.Access (oldSource hn ht ha) :=
  IntegralMixedFramedCoordinateCharacteristicBits.rootAccess (parameters (dimension n) (term t))
    (access (dimension_unary hn) (term_FP ht))
    (IntegralMixedAuxiliaryRecipeRoot.planAt hn ht ha) (IntegralMixedAuxiliaryRecipeRoot.dataAt hn ht ha)
    (inputSyntax hn ht ha)
    (IntegralMixedAuxiliaryEmptyPlan.familyInputs (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q)))
    (fun root => (IntegralMixedAuxiliaryEmptyPlan.description (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))).factor_positive root)
    (fun _ => by change 1≤1; exact le_rfl)

noncomputable def sourceContext (n : List Bool → ℕ) (t : List Bool → Term) (c : List Bool) :=
  pair (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id
    (IntegralMixedAuxiliaryCandidate.source n t (pairFst c))) (pairSnd c)

theorem sourceContext_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) : sourceContext n t∈FP :=
  by
    have HS := mem_FP_comp (f := pairFst) (g := IntegralMixedAuxiliaryCandidate.source n t)
      pairFst_mem_FP (IntegralMixedAuxiliaryCandidate.source_FP hn ht)
    have HK := IntegralMixedAuxiliaryPositivePrefix.key_FP (dimension_unary hn) id_mem_FP
    exact mem_FP_pair (mem_FP_comp (f := IntegralMixedAuxiliaryCandidate.source n t ∘ pairFst)
      (g := IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id) HS HK) pairSnd_mem_FP

noncomputable def coefficientQuery (n : List Bool → ℕ) (t : List Bool → Term) (z : List Bool) :=
  pair (pair (sourceContext n t (RationalSubstitution.IntegerBits.context z))
    (RationalSubstitution.IntegerBits.selectedDegree z)) (pairSnd z)

theorem coefficientQuery_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) : coefficientQuery n t∈FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (f := RationalSubstitution.IntegerBits.context)
    (g := sourceContext n t) RationalSubstitution.IntegerBits.context_mem_FP (sourceContext_FP hn ht))
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP

noncomputable def requerySource (S : IntegerPolynomialRootQueriesBits.Source) (f : List Bool → List Bool) : IntegerPolynomialRootQueriesBits.Source where
  polynomial c := S.polynomial (f c)
  degree c := S.degree (f c)
  mass c := S.mass (f c)
  degree_bound c := S.degree_bound (f c)
  mass_bound c := S.mass_bound (f c)

noncomputable def source {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :=
  requerySource (oldSource hn ht ha) (sourceContext n t)

private theorem coefficient_query (n : List Bool → ℕ) (t : List Bool → Term)
    (p : List Bool → Polynomial ℤ) (z : List Bool) :
    PrimitivePairBits.coefficient p (coefficientQuery n t z)=
      PrimitivePairBits.coefficient (p ∘ sourceContext n t) z := by
  simp only [PrimitivePairBits.coefficient,coefficientQuery,RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree,RationalSubstitution.IntegerBits.mValue,
    pairFst_pair,pairSnd_pair,Function.comp_apply]

attribute [local irreducible] sourceContext coefficientQuery PrimitivePairBits.coefficient

private theorem pullAccess (S : IntegerPolynomialRootQueriesBits.Source) (A : IntegerPolynomialRootQueriesBits.Access S)
    {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) :
    IntegerPolynomialRootQueriesBits.Access (requerySource S (sourceContext n t)) where
  degree := A.degree.comp (sourceContext_FP hn ht)
  mass := A.mass.comp (sourceContext_FP hn ht)
  coefficient := (A.coefficient.precompose (coefficientQuery n t) (coefficientQuery_FP hn ht)).congr
    (funext fun z => coefficient_query n t S.polynomial z)

attribute [local irreducible] source oldSource parameters scalarWidth scalarCeiling spatialDegree degreeCharge augmented

theorem native_access {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    IntegerPolynomialRootQueriesBits.Access (source hn ht ha) := by
  unfold source
  exact pullAccess (oldSource hn ht ha) (oldAccess hn ht ha) hn ht


end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateCoordinate
