/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateCoordinateSource
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateBounds
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicActual
/-! # The native coordinate source annihilates the same actual candidate point -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateCoordinate
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedAuxiliaryParameters
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open IntegralMixedAuxiliaryRecipeRoot (planAt dataAt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

 theorem context_active (n : List Bool → ℕ) (t : List Bool → Term) (c : List Bool) :
    IntegralMixedFramedCoordinateCharacteristicBits.Active (parameters (dimension n) (term t)) (sourceContext n t c) := by
  unfold IntegralMixedFramedCoordinateCharacteristicBits.Active IntegralMixedFramedCoordinateCharacteristicBits.key sourceContext
  rw [pairFst_pair,IntegralMixedAuxiliaryPositivePrefix.key_prefix]
  simp only [IntegralMixedAuxiliaryPositivePrefix.key,IntegralMixedFramedHistoryFamilyBits.keyAt,
    pairFst_pair,id_eq,parameters,horizon]
  omega

theorem context_count {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (c : List Bool) :
    IntegralMixedFramedCoordinateCharacteristicBits.count (parameters (dimension n) (term t))
      (planAt hn ht ha) (dataAt hn ht ha) (sourceContext n t c)=n (pairFst (pairFst c))+1 := by
  rw [IntegralMixedFramedCoordinateCharacteristicBits.count_eq]
  simp only [IntegralMixedFramedCoordinateCharacteristicBits.key,sourceContext,pairFst_pair]
  rw [IntegralMixedAuxiliaryPositivePrefix.key_prefix]
  simp only [dimension,id_eq,IntegralMixedAuxiliaryCandidate.source_input]

attribute [local irreducible] parameters scalarWidth scalarCeiling spatialDegree degreeCharge augmented planAt dataAt
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex
  IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryCandidate.bankData pair

theorem point_root {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : IntegralMixedAuxiliaryCandidate.Valid hn ht ha q) (i : Fin (n (pairFst q))) :
    ((source hn ht ha).polynomial (pair q (BinaryNatCode.encode (n (pairFst q)-i.val)))).eval₂
      (Int.castRingHom ℝ) (IntegralMixedAuxiliaryCandidate.point hn ht ha q hq i)=0 := by
  let c := sourceContext n t (pair q (BinaryNatCode.encode (n (pairFst q)-i.val)))
  have HI : IntegralMixedFramedCoordinateCharacteristicBits.index c <
      IntegralMixedFramedCoordinateCharacteristicBits.count (parameters (dimension n) (term t)) (planAt hn ht ha) (dataAt hn ht ha) c := by
    rw [context_count]
    simp only [c,sourceContext,IntegralMixedFramedCoordinateCharacteristicBits.index,pairSnd_pair,pairFst_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits]
    omega
  have HV : SquareSampleCompleteVertices.Valid (IntegralMixedAuxiliaryCandidateBounds.nativeInput hn ht ha)
      (IntegralMixedAuxiliaryCandidate.source n t q) (IntegralMixedAuxiliaryCandidate.vertex hn ht ha q) := by
    rw [IntegralMixedAuxiliaryCandidateBounds.nativeInput_eq]
    exact hq.2
  have HE := IntegralMixedAuxiliaryCandidateBounds.candidate_extend_congr _ _
    (IntegralMixedAuxiliaryCandidateBounds.nativeInput_eq hn ht ha).symm
    (IntegralMixedAuxiliaryCandidate.source n t q) (IntegralMixedAuxiliaryCandidate.vertex hn ht ha q) hq.2 HV
  have HK : IntegralMixedFramedCoordinateCharacteristicBits.key c=
      IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id (IntegralMixedAuxiliaryCandidate.source n t q) := by
    simp only [c,sourceContext,IntegralMixedFramedCoordinateCharacteristicBits.key,pairFst_pair]
  have HJ : IntegralMixedFramedCoordinateCharacteristicBits.index c=n (pairFst q)-i.val := by
    simp only [c,sourceContext,IntegralMixedFramedCoordinateCharacteristicBits.index,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HH := IntegralMixedFramedCoordinateCharacteristicBits.point_root
    (parameters (dimension n) (term t)) (planAt hn ht ha) (dataAt hn ht ha) c (context_active n t _) HI
  unfold IntegralMixedFramedCoordinateCharacteristicBits.count at HH
  rw [HK] at HH
  let HZ := (SquareSampleCompleteVertices.candidate (IntegralMixedAuxiliaryCandidateBounds.nativeInput hn ht ha)
    (IntegralMixedAuxiliaryCandidate.source n t q) (IntegralMixedAuxiliaryCandidate.vertex hn ht ha q) HV)
  have HHR := HH HZ.val HZ.property
  have Hpoly : (source hn ht ha).polynomial (pair q (BinaryNatCode.encode (n (pairFst q)-i.val)))=
      IntegralMixedFramedCoordinateCharacteristicBits.polynomial (parameters (dimension n) (term t))
        (planAt hn ht ha) (dataAt hn ht ha) c := rfl
  rw [Hpoly]
  have HP : IntegralMixedAuxiliaryCandidate.point hn ht ha q hq i=
      (IntegralMixedFramedBankObservation.ofState ((IntegralMixedFramedCoordinateCharacteristicBits.family
        (parameters (dimension n) (term t)) (planAt hn ht ha) (dataAt hn ht ha)).state
        (IntegralMixedFramedCoordinateCharacteristicBits.key c))).point
      (IntegralMixedFramedBankObservation.extend (SquareSampleCompleteVertices.candidate
        (IntegralMixedAuxiliaryCandidateBounds.nativeInput hn ht ha) (IntegralMixedAuxiliaryCandidate.source n t q)
        (IntegralMixedAuxiliaryCandidate.vertex hn ht ha q) HV).val)
      (IntegralMixedFramedCoordinateCharacteristicBits.index c) := by
    rw [HK,HJ]
    unfold IntegralMixedAuxiliaryCandidate.point IntegralMixedAuxiliaryCandidate.bankData IntegralMixedAuxiliaryCandidate.joint
    rw [HE]

  rw [HP]
  rw [HK]
  exact HHR

theorem pointAt_root {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original label : List Bool) (hq : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pair original label))
    (i : Fin (n original)) :
    ((source hn ht ha).polynomial (pair (pair original label) (BinaryNatCode.encode (n original-i.val)))).eval₂
      (Int.castRingHom ℝ) (IntegralMixedAuxiliaryCandidate.pointAt hn ht ha original label hq i)=0 := by
  unfold IntegralMixedAuxiliaryCandidate.pointAt
  simpa only [pairFst_pair] using point_root hn ht ha (pair original label) hq
    ⟨i.val,by simpa only [pairFst_pair] using i.isLt⟩

end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateCoordinate
