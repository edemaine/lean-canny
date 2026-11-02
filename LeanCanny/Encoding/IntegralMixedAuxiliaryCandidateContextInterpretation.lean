/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateInterpretation
public import LeanCanny.Geometry.IntegralMixedFramedObservedCoordinates
public import LeanCanny.Encoding.IntegralFramedSiblingRoots
public import LeanCanny.Algebra.IntegralMixedFramedBankObservationOrigin

/-! # Outer metadata keeps the same decoded original joint point

Sibling saved keys use the same root and chronological birth. One natural
joint tuple supplies both their row roots and bundled integer denominators.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateContextInterpretation
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask UniformIntegralPrefix
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open IntegralMixedAuxiliaryRecipeRoot (planAt dataAt)
open IntegralMixedAuxiliaryCandidateInterpretation (parameters key)
open IntegralMixedFramedSlackMatrixBits (elementAt commonAt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedAuxiliaryParameters.parameters
  IntegralMixedAuxiliaryParameters.scalarWidth IntegralMixedAuxiliaryParameters.scalarCeiling
  IntegralMixedAuxiliaryParameters.spatialDegree IntegralMixedAuxiliaryParameters.degreeCharge
  IntegralMixedAuxiliaryParameters.augmented planAt dataAt
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex
  IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryCandidate.point
  IntegralMixedAuxiliaryCandidate.bankData IntegralMixedAuxiliaryCandidate.joint pair
  IntegralMixedFramedHistoryFamilyBits.family

theorem joint_roots {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : IntegralMixedAuxiliaryCandidate.Valid hn ht ha q) :
    RootsAt ((IntegralMixedFramedHistoryFamilyBits.family (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)).state
      (key n t q)).sampler.scalarPrefix (IntegralMixedAuxiliaryCandidate.joint hn ht ha q hq) := by
  have HV : SquareSampleCompleteVertices.Valid (IntegralMixedAuxiliaryCandidateBounds.nativeInput hn ht ha)
      (IntegralMixedAuxiliaryCandidate.source n t q) (IntegralMixedAuxiliaryCandidate.vertex hn ht ha q) := by
    rw [IntegralMixedAuxiliaryCandidateBounds.nativeInput_eq]
    exact hq.2
  have HE:=IntegralMixedAuxiliaryCandidateBounds.candidate_extend_congr _ _
    (IntegralMixedAuxiliaryCandidateBounds.nativeInput_eq hn ht ha).symm
    (IntegralMixedAuxiliaryCandidate.source n t q) (IntegralMixedAuxiliaryCandidate.vertex hn ht ha q) hq.2 HV
  have HJ : IntegralMixedAuxiliaryCandidate.joint hn ht ha q hq=
      IntegralFramedCompleteSuffix.joint (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) (fun _=>1)
        (IntegralMixedAuxiliarySchedule.factor (dimension n) (term t)) (IntegralMixedAuxiliarySchedule.seed (dimension n) (term t))
        (IntegralMixedAuxiliaryCandidateBounds.family_inputs hn ht ha) (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id)
        (IntegralMixedAuxiliaryCandidateBounds.positive hn ht ha) (IntegralMixedAuxiliaryCandidate.source n t q)
        (IntegralMixedAuxiliaryCandidate.vertex hn ht ha q) HV := by
    unfold IntegralMixedAuxiliaryCandidate.joint IntegralFramedCompleteSuffix.joint
    exact HE
  have HR:=IntegralFramedCompleteSuffix.terminal_roots (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) (fun _=>1)
    (IntegralMixedAuxiliarySchedule.factor (dimension n) (term t)) (IntegralMixedAuxiliarySchedule.seed (dimension n) (term t))
    (IntegralMixedAuxiliaryCandidateBounds.family_inputs hn ht ha) (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id)
    (IntegralMixedAuxiliaryCandidateBounds.positive hn ht ha) (IntegralMixedAuxiliaryCandidate.source n t q)
    (IntegralMixedAuxiliaryCandidate.vertex hn ht ha q) HV
  have HR0 : RootsAt ((IntegralMixedFramedHistoryFamilyBits.family (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)).state
      (key n t q)).sampler.scalarPrefix (IntegralMixedAuxiliaryCandidate.joint hn ht ha q hq) :=
    Eq.mpr (congrArg (RootsAt ((IntegralMixedFramedHistoryFamilyBits.family (parameters n t) (planAt hn ht ha)
      (dataAt hn ht ha)).state (key n t q)).sampler.scalarPrefix) HJ) HR
  exact HR0

private theorem sibling_birth {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q k : List Bool)
    (hb : IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key n t q)=
      IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) k) :
    (IntegralMixedFramedHistoryFamilyBits.family (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)).birth k=n (pairFst q)+1 := by
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth,←hb,key,IntegralMixedAuxiliaryPositivePrefix.key_prefix]
  exact congrArg (fun r=>n r+1) (IntegralMixedAuxiliaryCandidate.source_input n t q)

private theorem sibling_active {n : List Bool→ℕ} {t : List Bool→Term}
    (q k : List Bool) (hr : pairFst (key n t q)=pairFst k)
    (hb : IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key n t q)=
      IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) k) :
    IntegralMixedFramedClearedMatrixBits.Active (parameters n t) k := by
  unfold IntegralMixedFramedClearedMatrixBits.Active
  rw [←hr,←hb]
  have H:=IntegralMixedAuxiliaryCandidateCoordinate.context_active n t (pair q [])
  simpa only [IntegralMixedFramedCoordinateCharacteristicBits.Active,IntegralMixedFramedCoordinateCharacteristicBits.key,
    IntegralMixedAuxiliaryCandidateCoordinate.sourceContext,key,pairFst_pair] using H

theorem exists_at_sibling {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : IntegralMixedAuxiliaryCandidate.Valid hn ht ha q) (k : List Bool)
    (hr : pairFst (key n t q)=pairFst k)
    (hb : IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key n t q)=
      IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) k) :
    ∃ φ : ((IntegralMixedFramedHistoryFamilyBits.family (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)).state k).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀ i : Fin (n (pairFst q)),φ (elementAt (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) k
        (n (pairFst q)-i.val))=(commonAt (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) k : ℝ)*
          IntegralMixedAuxiliaryCandidate.point hn ht ha q hq i := by
  have HR0:=joint_roots hn ht ha q hq
  have HRK:=(IntegralFramedSiblingRoots.roots_sibling (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) (dataAt hn ht ha)
    (key n t q) k hr hb (IntegralMixedAuxiliaryCandidate.joint hn ht ha q hq)).mp HR0
  have HD:=IntegralMixedFramedBankObservation.data_sibling (parameters n t) (planAt hn ht ha)
    (dataAt hn ht ha) (dataAt hn ht ha) k (key n t q) hr.symm hb.symm
  have HC:=sibling_birth hn ht ha q k hb
  have HA:=sibling_active q k hr hb
  apply IntegralMixedFramedObservedCoordinates.exists_interpretation (parameters n t) (planAt hn ht ha)
    (dataAt hn ht ha) k HA (n (pairFst q)) (by rw [HC]; omega)
    (IntegralMixedAuxiliaryCandidate.joint hn ht ha q hq) HRK (IntegralMixedAuxiliaryCandidate.point hn ht ha q hq)
  intro i
  unfold IntegralMixedAuxiliaryCandidate.point IntegralMixedAuxiliaryCandidate.bankData
  exact congrArg (fun d : IntegralMixedFramedBankObservation.Data=>d.point
    (IntegralMixedAuxiliaryCandidate.joint hn ht ha q hq) (n (pairFst q)-i.val)) HD

end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateContextInterpretation
