/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFramedSlackJointInterpretation
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateCoordinateRoot

/-! # The decoded original candidate constructs its one old interpretation

All original coordinates are read from the same literal complete candidate.
No interpreting hom or independent coordinate roots are supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateInterpretation
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open IntegralMixedAuxiliaryRecipeRoot (planAt dataAt)
open IntegralMixedFramedSlackMatrixBits (elementAt commonAt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev parameters (n : List Bool→ℕ) (t : List Bool→Term) :=
  IntegralMixedAuxiliaryParameters.parameters (dimension n) (term t)
noncomputable def key (n : List Bool→ℕ) (t : List Bool→Term) (q : List Bool) :=
  IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id (IntegralMixedAuxiliaryCandidate.source n t q)

attribute [local irreducible] IntegralMixedAuxiliaryParameters.parameters
  IntegralMixedAuxiliaryParameters.scalarWidth IntegralMixedAuxiliaryParameters.scalarCeiling
  IntegralMixedAuxiliaryParameters.spatialDegree IntegralMixedAuxiliaryParameters.degreeCharge
  IntegralMixedAuxiliaryParameters.augmented planAt dataAt
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex
  IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryCandidate.point
  IntegralMixedAuxiliaryCandidate.bankData IntegralMixedAuxiliaryCandidate.joint pair
  IntegralMixedFramedHistoryFamilyBits.family

theorem exists_interpretation {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : IntegralMixedAuxiliaryCandidate.Valid hn ht ha q) :
    ∃ φ : ((IntegralMixedFramedHistoryFamilyBits.family (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)).state
        (key n t q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀ i : Fin (n (pairFst q)),φ (elementAt (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)
        (key n t q) (n (pairFst q)-i.val))=(commonAt (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) (key n t q) : ℝ)*
          IntegralMixedAuxiliaryCandidate.point hn ht ha q hq i := by
  have HV : SquareSampleCompleteVertices.Valid (IntegralMixedAuxiliaryCandidateBounds.nativeInput hn ht ha)
      (IntegralMixedAuxiliaryCandidate.source n t q) (IntegralMixedAuxiliaryCandidate.vertex hn ht ha q) := by
    rw [IntegralMixedAuxiliaryCandidateBounds.nativeInput_eq]
    exact hq.2
  let Z:=SquareSampleCompleteVertices.candidate (IntegralMixedAuxiliaryCandidateBounds.nativeInput hn ht ha)
    (IntegralMixedAuxiliaryCandidate.source n t q) (IntegralMixedAuxiliaryCandidate.vertex hn ht ha q) HV
  let x:=(IntegralMixedFramedHistoryFamilyBits.family (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)).state (key n t q)
  have HC : (IntegralMixedFramedHistoryFamilyBits.family (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)).birth
      (key n t q)=n (pairFst q)+1 := by
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth,key,IntegralMixedAuxiliaryPositivePrefix.key_prefix]
    exact congrArg (fun r=>n r+1) (IntegralMixedAuxiliaryCandidate.source_input n t q)
  have HA : IntegralMixedFramedClearedMatrixBits.Active (parameters n t) (key n t q) := by
    have H:=IntegralMixedAuxiliaryCandidateCoordinate.context_active n t (pair q [])
    simpa only [IntegralMixedFramedClearedMatrixBits.Active,IntegralMixedFramedCoordinateCharacteristicBits.Active,
      IntegralMixedFramedCoordinateCharacteristicBits.key,IntegralMixedAuxiliaryCandidateCoordinate.sourceContext,
      key,pairFst_pair] using H
  have HE:=IntegralMixedAuxiliaryCandidateBounds.candidate_extend_congr _ _
    (IntegralMixedAuxiliaryCandidateBounds.nativeInput_eq hn ht ha).symm
    (IntegralMixedAuxiliaryCandidate.source n t q) (IntegralMixedAuxiliaryCandidate.vertex hn ht ha q) hq.2 HV
  refine IntegralMixedFramedSlackJointInterpretation.exists_coordinate_interpretation
    (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) (key n t q) HA (n (pairFst q))
    (by rw [HC]; omega) Z.val Z.property (IntegralMixedAuxiliaryCandidate.point hn ht ha q hq) ?_
  intro i
  have HI : n (pairFst q)-i.val<(IntegralMixedFramedHistoryFamilyBits.family (parameters n t)
      (planAt hn ht ha) (dataAt hn ht ha)).birth (key n t q) := by rw [HC]; omega
  let j : Fin ((IntegralMixedFramedHistoryFamilyBits.family (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)).birth
    (key n t q)):=⟨n (pairFst q)-i.val,HI⟩
  have HEJ : IntegralMixedAuxiliaryCandidate.joint hn ht ha q hq=IntegralMixedFramedBankObservation.extend Z.val := by
    unfold IntegralMixedAuxiliaryCandidate.joint
    exact HE
  have HP : IntegralMixedAuxiliaryCandidate.point hn ht ha q hq i=IntegralMixedCanonicalBankPoint.point x Z.val j := by
    have HS : IntegralMixedAuxiliaryCandidate.point hn ht ha q hq i=
        (IntegralMixedAuxiliaryCandidate.bankData hn ht ha (IntegralMixedAuxiliaryCandidate.source n t q)).point
          (IntegralMixedFramedBankObservation.extend Z.val) (n (pairFst q)-i.val) := by
      unfold IntegralMixedAuxiliaryCandidate.point
      exact congrArg (fun v : ℕ→ℝ=>(IntegralMixedAuxiliaryCandidate.bankData hn ht ha
        (IntegralMixedAuxiliaryCandidate.source n t q)).point v (n (pairFst q)-i.val)) HEJ
    refine HS.trans ?_
    unfold IntegralMixedAuxiliaryCandidate.bankData
    exact IntegralMixedFramedBankObservation.point_ofState x Z.val j
  exact HP.symm

end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateInterpretation
