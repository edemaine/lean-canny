/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapPaddedWord
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateLabel
public import LeanCanny.Computation.WordResourceEnvelope
/-! # Scalar-width snapshots before allocating recursive records

Replacing a record table or its original metadata changes neither the marked
scalar width nor the original integer degree ceiling. These are numeric
identities, not equivalences between sample words at different roots.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapWidth
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem rank_context (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (root c e : List Bool) (b : ℕ) :
    IntegralMixedFramedClearedMatrixBits.rank P D H (IntegralMixedFramedHistoryFamilyBits.keyAt root b c)=
      IntegralMixedFramedClearedMatrixBits.rank P D H (IntegralMixedFramedHistoryFamilyBits.keyAt root b e) :=by
  unfold IntegralMixedFramedClearedMatrixBits.rank IntegralMixedFramedClearedMatrixBits.family
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth,IntegralMixedFramedHistoryFamilyBits.family_birth]
  simp only [IntegralMixedFramedHistoryFamilyBits.prefixLength,IntegralMixedFullHistoryFamilyBits.prefixLength,
    IntegralMixedFramedHistoryFamilyBits.keyAt,IntegralMixedFramedHistoryFamilyBits.family,pairFst_pair,pairSnd_pair]

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)

attribute [local irreducible] IntegralMixedFramedClearedMatrixBits.rank
  IntegralMixedAuxiliaryRecipeRoot.planAt IntegralMixedAuxiliaryRecipeRoot.dataAt
  IntegralMixedAuxiliarySlackSource.syntaxInput

theorem sphereDegree_context (candidate c e : List Bool) :
    IntegralMixedAuxiliaryMarkedIntegerSource.sphereDegree hn ht ha (pair candidate c)=
      IntegralMixedAuxiliaryMarkedIntegerSource.sphereDegree hn ht ha (pair candidate e) :=by
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.sphereDegree,
    IntegralMixedAuxiliaryParametricSlackSource.sphereSource,IntegralMixedFramedSlackRootBits.sphereSource,
    IntegerPolynomialExpandSource.source,IntegralMixedFramedSlackRootBits.rawSphereSource]
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.oldKey,IntegralMixedAuxiliaryMarkedIntegerSource.number,
    IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,pairFst_pair]
  rw [rank_context _ _ _ _ (pair candidate c) (pair candidate e)]

theorem regularDegree_context (candidate c e : List Bool) :
    IntegralMixedAuxiliaryMarkedIntegerSource.regularDegree hn ht ha (pair candidate c)=
      IntegralMixedAuxiliaryMarkedIntegerSource.regularDegree hn ht ha (pair candidate e) :=by
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.regularDegree,
    IntegralMixedAuxiliaryParametricSlackSource.regularSource,IntegralMixedFramedSlackRootBits.regularSource,
    IntegerPolynomialExpandSource.source,IntegralMixedFramedSlackRootBits.rawRegularSource]
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.oldKey,IntegralMixedAuxiliaryMarkedIntegerSource.number,
    IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,pairFst_pair]
  rw [rank_context _ _ _ _ (pair candidate c) (pair candidate e)]
  simp only [IntegralMixedAuxiliarySlackMatrix.degree,IntegralMixedAuxiliarySlackMatrix.charge,
    IntegralMixedAuxiliarySlackMatrix.original,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]

theorem coordinateDegree_context (candidate c e : List Bool) :
    IntegralMixedAuxiliaryMarkedIntegerSource.coordinateDegree hn ht ha (pair candidate c)=
      IntegralMixedAuxiliaryMarkedIntegerSource.coordinateDegree hn ht ha (pair candidate e) :=by
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.coordinateDegree,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,pairFst_pair]

attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerSource.coordinateDegree
  IntegralMixedAuxiliaryMarkedIntegerSource.sphereDegree IntegralMixedAuxiliaryMarkedIntegerSource.regularDegree

theorem degreeBound_context (candidate c e : List Bool) :
    IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound hn ht ha (pair candidate c)=
      IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound hn ht ha (pair candidate e) :=by
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound,
    coordinateDegree_context hn ht ha candidate c e,
    sphereDegree_context hn ht ha candidate c e,regularDegree_context hn ht ha candidate c e]

attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound

theorem width_context (candidate c e : List Bool) :
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width (pair candidate c)=
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width (pair candidate e) :=by
  simp only [IntegralMixedAuxiliaryMarkedRecordPlan.parameters,IntegralMixedSourceIntegerPrelude.parameters,
    IntegralMixedSourceIntegerPrelude.ceiling]
  rw [degreeBound_context hn ht ha candidate c e]
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedAuxiliaryMarkedIntegerPlan.degree,pairFst_pair]

noncomputable def baseline (candidate : List Bool) :=
  (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width (pair candidate [])

theorem baseline_unary : UnaryFn (baseline hn ht ha) :=
  (IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).width.comp
    (mem_FP_pair id_mem_FP (constFn_mem_FP []))

noncomputable def candidateBudget (original : List Bool) :=
  2*original.length+2+IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original

theorem candidateBudget_unary : UnaryFn (candidateBudget hn ht ha) :=
  (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 2)).add
    (IntegralMixedAuxiliaryCandidate.labelWidth_unary hn ht ha)

theorem candidate_length (original label : List Bool)
    (hlabel : label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original) :
    (pair original label).length≤candidateBudget hn ht ha original :=by
  rw [pair_length]
  exact Nat.add_le_add_left hlabel _

theorem exists_scalarBudget : ∃ B : List Bool→ℕ, UnaryFn B ∧
    ∀ original label c, label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original →
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width (pair (pair original label) c)≤B original :=by
  obtain ⟨B,hB,hbound⟩:=(baseline_unary hn ht ha).wordEnvelope (candidateBudget_unary hn ht ha)
  refine ⟨B,hB,?_⟩
  intro original label c hlabel
  rw [width_context hn ht ha _ c []]
  exact hbound original (pair original label) (candidate_length hn ht ha original label hlabel)

noncomputable def scalarBudget : List Bool→ℕ :=Classical.choose (exists_scalarBudget hn ht ha)

theorem scalarBudget_unary : UnaryFn (scalarBudget hn ht ha) :=
  (Classical.choose_spec (exists_scalarBudget hn ht ha)).1

theorem width_le_scalarBudget (original label c : List Bool)
    (hlabel : label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original) :
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width (pair (pair original label) c)≤
      scalarBudget hn ht ha original :=
  (Classical.choose_spec (exists_scalarBudget hn ht ha)).2 original label c hlabel

end LeanCanny.Encoding.IntegralMixedRoadmapWidth
