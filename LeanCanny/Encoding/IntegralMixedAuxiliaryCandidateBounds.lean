/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFramedBankPointBound
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidatePointSampling
public import LeanCanny.Computation.WordResourceEnvelope

/-! # Original-controlled real bounds for every decoded joint candidate

Actual bank matrix bounds control the same interpreted joint-root coordinates.
A later regular-source radius is not used to bound its own input candidates.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateBounds
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR LeanCanny.Geometry
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule IntegralMixedAuxiliaryRecipeRoot
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open IntegralMixedFramedBankObservation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem family_inputs {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    IntegralMixedFramedStepHeight.FamilyInputs (parameters (dimension n) (term t)) (planAt hn ht ha)
      (fun _=>1) (factor (dimension n) (term t)) (seed (dimension n) (term t)) := by
  unfold planAt
  exact IntegralMixedAuxiliaryEmptyPlan.familyInputs (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
    (IntegralMixedAuxiliaryPreparedRoot.term_FP ht) (fun q=>ha (pairFst q))

theorem positive {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (packed : List Bool) :
    0<(IntegralMixedFramedHistoryFamilyBits.family (parameters (dimension n) (term t)) (planAt hn ht ha) (dataAt hn ht ha)).birth
      (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id packed) :=
  (IntegralMixedAuxiliaryPositivePrefix.key_positive (dimension n) (term t) id packed).trans_eq
    (IntegralMixedFramedHistoryFamilyBits.family_birth (parameters (dimension n) (term t)) (planAt hn ht ha) (dataAt hn ht ha) _).symm

noncomputable def nativeInput {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :=
  IntegralFramedCompleteSquare.input (parameters (dimension n) (term t)) (planAt hn ht ha) (dataAt hn ht ha)
    (fun _=>1) (factor (dimension n) (term t)) (seed (dimension n) (term t)) (family_inputs hn ht ha)
    (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id) (positive hn ht ha)

theorem nativeInput_eq {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    nativeInput hn ht ha=IntegralMixedAuxiliaryCandidate.input hn ht ha := by
  unfold nativeInput IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryPositivePrefix.input
    IntegralMixedAuxiliaryEmptyPlan.squareInput planAt dataAt
  rfl

noncomputable def packedHeight {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (packed : List Bool) :=
  IntegralMixedFramedBankPointBound.height (parameters (dimension n) (term t)) (planAt hn ht ha) (dataAt hn ht ha)
    (fun _=>1) (factor (dimension n) (term t)) (seed (dimension n) (term t))
    (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id packed)

theorem packedHeight_binary {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    BinaryFn (packedHeight hn ht ha) :=
  (IntegralMixedFramedBankPointBound.height_binary (parameters (dimension n) (term t))
    (IntegralMixedAuxiliaryParameters.access (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
      (IntegralMixedAuxiliaryPreparedRoot.term_FP ht)) (planAt hn ht ha) (dataAt hn ht ha)
    (BinaryFn.const 1) (factor_binary (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn) (IntegralMixedAuxiliaryPreparedRoot.term_FP ht))
    (seed_binary (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn) (IntegralMixedAuxiliaryPreparedRoot.term_FP ht))).comp
      (IntegralMixedAuxiliaryPositivePrefix.key_FP (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn) id_mem_FP)

theorem candidate_extend_congr (F G : SquareSampleInput.Inputs) (he : F=G) (u w : List Bool)
    (hf : SquareSampleCompleteVertices.Valid F u w) (hg : SquareSampleCompleteVertices.Valid G u w) :
    extend (SquareSampleCompleteVertices.candidate F u w hf).val=extend (SquareSampleCompleteVertices.candidate G u w hg).val := by
  cases he
  rfl

attribute [local irreducible] parameters scalarWidth scalarCeiling spatialDegree degreeCharge augmented root planAt dataAt
  packedHeight nativeInput IntegralMixedAuxiliaryPositivePrefix.key pair
  IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryCandidate.bankData
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex IntegralMixedAuxiliaryCandidate.joint

theorem point_bound {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : IntegralMixedAuxiliaryCandidate.Valid hn ht ha q) (i : Fin (n (pairFst q))) :
    |IntegralMixedAuxiliaryCandidate.point hn ht ha q hq i|≤(2:ℝ)^packedHeight hn ht ha (IntegralMixedAuxiliaryCandidate.source n t q) := by
  have HV : SquareSampleCompleteVertices.Valid (nativeInput hn ht ha)
      (IntegralMixedAuxiliaryCandidate.source n t q) (IntegralMixedAuxiliaryCandidate.vertex hn ht ha q) := by
    rw [nativeInput_eq]
    exact hq.2
  have HE := candidate_extend_congr _ _ (nativeInput_eq hn ht ha).symm
    (IntegralMixedAuxiliaryCandidate.source n t q) (IntegralMixedAuxiliaryCandidate.vertex hn ht ha q) hq.2 HV
  unfold nativeInput at HV
  have HB:=IntegralMixedFramedBankPointBound.sample_bound (parameters (dimension n) (term t)) (planAt hn ht ha) (dataAt hn ht ha)
    (fun _=>1) (factor (dimension n) (term t)) (seed (dimension n) (term t)) (family_inputs hn ht ha)
    (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id) (positive hn ht ha)
    (IntegralMixedAuxiliaryCandidate.source n t q) (IntegralMixedAuxiliaryCandidate.vertex hn ht ha q) HV (n (pairFst q)-i.val)
  unfold IntegralMixedAuxiliaryCandidate.point IntegralMixedAuxiliaryCandidate.joint
    IntegralMixedAuxiliaryCandidate.bankData packedHeight
  rw [HE]
  unfold nativeInput
  exact HB

theorem pointAt_bound {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original label : List Bool) (hv : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pair original label)) (i : Fin (n original)) :
    |IntegralMixedAuxiliaryCandidate.pointAt hn ht ha original label hv i|≤
      (2:ℝ)^packedHeight hn ht ha (IntegralMixedAuxiliaryCandidate.source n t (pair original label)) := by
  unfold IntegralMixedAuxiliaryCandidate.pointAt
  exact point_bound hn ht ha _ hv _

end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateBounds
