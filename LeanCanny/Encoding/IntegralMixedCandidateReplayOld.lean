/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCandidateReplayDatum
public import LeanCanny.Encoding.IntegralFramedBankUnivariateLegacy
public import LeanCanny.Algebra.ThomEncoding
/-! # Datum-selected tests at the literal original candidate

The sampler context is exactly Candidate.source and its label exactly
Candidate.vertex. Neither coordinate nor derivative changes that sampler.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCandidateReplayOld
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryPreparedRoot (dimension term dimension_unary term_FP)
open IntegralMixedAuxiliaryRecipeRoot (planAt dataAt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)

noncomputable abbrev parameters := IntegralMixedAuxiliaryParameters.parameters (dimension n) (term t)
noncomputable abbrev key := IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id
noncomputable abbrev input := IntegralMixedAuxiliaryCandidateBounds.nativeInput hn ht ha

noncomputable def originalSyntax : IntegralMixedFramedNativeBits.Syntax (parameters (n:=n) (t:=t)) (planAt hn ht ha) (dataAt hn ht ha) :=
  IntegralMixedAuxiliaryCandidateCoordinate.inputSyntax hn ht ha

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedAuxiliaryParameters.parameters IntegralMixedAuxiliaryParameters.scalarWidth
  IntegralMixedAuxiliaryParameters.scalarCeiling IntegralMixedAuxiliaryParameters.spatialDegree
  IntegralMixedAuxiliaryParameters.degreeCharge IntegralMixedAuxiliaryParameters.augmented planAt dataAt

noncomputable def count (c : List Bool) : ℕ :=
  (IntegralMixedFramedBankSnapshotBits.atKey (parameters (n:=n) (t:=t)) (planAt hn ht ha) (dataAt hn ht ha) (key (n:=n) c)).count

noncomputable def coordinate (c d : List Bool) : Fin (count hn ht ha c) :=
  ⟨min (IntegralMixedCandidateReplayDatum.retained n d) (count hn ht ha c-1),by
    have H:=IntegralMixedAuxiliaryCandidateBounds.positive hn ht ha c
    change 0<count hn ht ha c at H
    have HL:=min_le_right (IntegralMixedCandidateReplayDatum.retained n d) (count hn ht ha c-1)
    omega⟩

theorem count_eq (c : List Bool) : count hn ht ha c=n (pairFst c)+1 := by
  change (IntegralMixedFramedHistoryFamilyBits.family (parameters (n:=n) (t:=t)) (planAt hn ht ha) (dataAt hn ht ha)).birth (key (n:=n) c)=_
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth,IntegralMixedAuxiliaryPositivePrefix.key_prefix]
  rfl

theorem coordinate_unary : UnaryFn ((fun z=>(coordinate hn ht ha (pairFst z) (pairSnd z)).val)) := by
  have HC : UnaryFn (fun z=>count hn ht ha (pairFst z)-1) :=
    (((hn.comp pairFst_mem_FP).add (UnaryFn.const 1)).comp pairFst_mem_FP).sub (UnaryFn.const 1) |>.of_eq
      (fun z=>by rw [count_eq])
  have HR : BinaryFn (fun z=>IntegralMixedCandidateReplayDatum.retained n (pairSnd z)) :=
    (IntegralMixedCandidateReplayDatum.retained_binary hn).comp pairSnd_mem_FP
  apply (UnaryFn.fromBitsLE_min HR.bits_mem_FP HC).of_eq
  intro z
  simp only [coordinate,BinaryNatCode.encode,Nat.fromBitsLE_bits]

noncomputable def value : List Bool→List Bool := IntegralFramedBankUnivariateTest.value (parameters (n:=n) (t:=t)) (planAt hn ht ha) (dataAt hn ht ha)
  (fun _=>1) (IntegralMixedAuxiliarySchedule.factor (dimension n) (term t)) (IntegralMixedAuxiliarySchedule.seed (dimension n) (term t))
  (IntegralMixedAuxiliaryCandidateBounds.family_inputs hn ht ha) (key (n:=n)) (IntegralMixedAuxiliaryCandidateBounds.positive hn ht ha)
  (coordinate hn ht ha) (IntegralMixedCandidateReplayDatum.source hn ht ha)


attribute [local irreducible] coordinate IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex

theorem evaluator : SpaceFunction (value hn ht ha) :=
  IntegralFramedBankUnivariateLegacy.evaluator (parameters (n:=n) (t:=t))
    (IntegralMixedAuxiliaryParameters.access (dimension_unary hn) (term_FP ht)) (planAt hn ht ha) (dataAt hn ht ha)
    (originalSyntax hn ht ha) (IntegralMixedAuxiliaryCandidateBounds.family_inputs hn ht ha)
    (fun root=>(IntegralMixedAuxiliaryEmptyPlan.description (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))).factor_positive root)
    (fun _=>le_rfl) (BinaryFn.const 1) (IntegralMixedAuxiliarySchedule.factor_binary (dimension_unary hn) (term_FP ht))
    (IntegralMixedAuxiliarySchedule.seed_binary (dimension_unary hn) (term_FP ht))
    (IntegralMixedAuxiliaryCandidateBounds.family_inputs hn ht ha) (key (n:=n))
    (IntegralMixedAuxiliaryPositivePrefix.key_FP (dimension_unary hn) id_mem_FP) (IntegralMixedAuxiliaryCandidateBounds.positive hn ht ha)
    (coordinate hn ht ha) (coordinate_unary hn ht ha) _ (IntegralMixedCandidateReplayDatum.access hn ht ha)

attribute [local irreducible] value IntegralMixedCandidateReplayDatum.source IntegralMixedAuxiliaryCandidateCoordinate.source
  IntegralFramedBankUnivariateTest.value LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point

theorem packet (p : List Bool) (hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha p)
    (i : Fin (n (pairFst p))) (k : ℕ) :
    value hn ht ha (pair (IntegralMixedAuxiliaryCandidate.packet hn ht ha p) (IntegralMixedCandidateReplayDatum.packet p i.val k))=
      InfinitesimalSign.encode (ThomEncoding.sign
        (((IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).polynomial
          (pair p (BinaryNatCode.encode (n (pairFst p)-i.val)))).map (Int.castRingHom ℝ))
        (IntegralMixedAuxiliaryCandidate.point hn ht ha p hp i) k) := by
  have HV : SquareSampleCompleteVertices.Valid (input hn ht ha)
      (IntegralMixedAuxiliaryCandidate.source n t p) (IntegralMixedAuxiliaryCandidate.vertex hn ht ha p) := by
    change SquareSampleCompleteVertices.Valid (IntegralMixedAuxiliaryCandidateBounds.nativeInput hn ht ha) _ _
    rw [IntegralMixedAuxiliaryCandidateBounds.nativeInput_eq]
    exact hp.2
  have HE:=IntegralMixedAuxiliaryCandidateBounds.candidate_extend_congr _ _
    (IntegralMixedAuxiliaryCandidateBounds.nativeInput_eq hn ht ha)
    (IntegralMixedAuxiliaryCandidate.source n t p) (IntegralMixedAuxiliaryCandidate.vertex hn ht ha p) HV hp.2
  have HI : (coordinate hn ht ha (IntegralMixedAuxiliaryCandidate.source n t p)
      (IntegralMixedCandidateReplayDatum.packet p i.val k)).val=n (pairFst p)-i.val := by
    rw [coordinate]
    simp only [IntegralMixedCandidateReplayDatum.retained,IntegralMixedCandidateReplayDatum.candidate,
      IntegralMixedCandidateReplayDatum.index,IntegralMixedCandidateReplayDatum.packet,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits]
    rw [count_eq,IntegralMixedAuxiliaryCandidate.source_input]
    omega
  have HP:=IntegralFramedBankUnivariateTest.packet (parameters (n:=n) (t:=t)) (planAt hn ht ha) (dataAt hn ht ha)
    (fun _=>1) (IntegralMixedAuxiliarySchedule.factor (dimension n) (term t)) (IntegralMixedAuxiliarySchedule.seed (dimension n) (term t))
    (IntegralMixedAuxiliaryCandidateBounds.family_inputs hn ht ha) (key (n:=n)) (IntegralMixedAuxiliaryCandidateBounds.positive hn ht ha)
    (coordinate hn ht ha) (IntegralMixedCandidateReplayDatum.source hn ht ha)
    (IntegralMixedAuxiliaryCandidate.source n t p) (IntegralMixedAuxiliaryCandidate.vertex hn ht ha p)
    (IntegralMixedCandidateReplayDatum.packet p i.val k) HV
  have HX:=IntegralMixedFramedBankObservation.point_ofState
    (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state (parameters (n:=n) (t:=t)) (planAt hn ht ha) (dataAt hn ht ha)
      (key (n:=n) (IntegralMixedAuxiliaryCandidate.source n t p)))
    (SquareSampleCompleteVertices.candidate (input hn ht ha) (IntegralMixedAuxiliaryCandidate.source n t p)
      (IntegralMixedAuxiliaryCandidate.vertex hn ht ha p) HV).val
    (coordinate hn ht ha (IntegralMixedAuxiliaryCandidate.source n t p) (IntegralMixedCandidateReplayDatum.packet p i.val k))
  have HObs :
      (IntegralMixedFramedBankObservation.ofState (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state
        (parameters (n:=n) (t:=t)) (planAt hn ht ha) (dataAt hn ht ha)
        (key (n:=n) (IntegralMixedAuxiliaryCandidate.source n t p)))).point
        (IntegralMixedFramedBankObservation.extend (SquareSampleCompleteVertices.candidate (input hn ht ha)
          (IntegralMixedAuxiliaryCandidate.source n t p) (IntegralMixedAuxiliaryCandidate.vertex hn ht ha p) HV).val)
        (coordinate hn ht ha (IntegralMixedAuxiliaryCandidate.source n t p) (IntegralMixedCandidateReplayDatum.packet p i.val k)).val=
      IntegralMixedAuxiliaryCandidate.point hn ht ha p hp i := by
    rw [HI,HE]
    rfl
  have HPoint:=HX.symm.trans HObs
  have HPoly:=IntegralMixedCandidateReplayDatum.polynomial_packet hn ht ha (IntegralMixedAuxiliaryCandidate.source n t p) p i.val k
  have HValue:=congrArg₂ (fun (f : Polynomial ℤ) (v : ℝ)=>f.eval₂ (Int.castRingHom ℝ) v) HPoly HPoint
  have HResult:=HP.trans (congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v)) HValue)
  simpa only [value,IntegralMixedAuxiliaryCandidate.packet,
    ThomEncoding.sign,Polynomial.iterate_derivative_map,Polynomial.eval_map] using HResult

end LeanCanny.Encoding.IntegralMixedCandidateReplayOld
