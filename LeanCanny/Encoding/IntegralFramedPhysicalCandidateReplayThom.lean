/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCandidateReplayOld
public import LeanCanny.Encoding.IntegralFramedPhysicalCandidateReplay
public import LeanCanny.Computation.SpaceFunctionBinaryQuantifiers
public import LeanCanny.Computation.SpaceFunctionQuantifiers
/-! # Native original-coordinate equality of old candidates and full physical replays

The outer packet is `(marked context, marked vertex)`, with marked context
`(old candidate packet, outer metadata)`. Unary coordinate and binary derivative
scans change only the shared test datum. Both the original and full physical sampler contexts and
vertex labels remain literal and fixed throughout every scan.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalCandidateReplayThom
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralFramedBankQuery (Bank)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
  (B : Bank)

def context (q : List Bool) := pairFst q
def word (q : List Bool) := pairSnd (pairSnd q)
def target (q : List Bool) := pairFst (pairSnd q)
theorem target_FP : target∈FP := by polytime [target]
theorem word_FP : word∈FP := by polytime [word]
def oldCandidate (q : List Bool) := pairFst (context q)
def dimension (n : List Bool→ℕ) (q : List Bool) := n (pairFst (oldCandidate q))
theorem oldCandidate_FP : oldCandidate∈FP:=mem_FP_comp pairFst_mem_FP pairFst_mem_FP
include hn in
theorem dimension_unary : UnaryFn (dimension n):=hn.comp (mem_FP_comp oldCandidate_FP pairFst_mem_FP)

def boundContext (n : List Bool→ℕ) (z : List Bool) := pair (oldCandidate (pairFst z))
  (BinaryNatCode.encode (dimension n (pairFst z)-(pairSnd z).length))
include hn in
theorem boundContext_FP : boundContext n∈FP := by
  have HN : UnaryFn (fun z=>dimension n (pairFst z)) := (dimension_unary hn).comp pairFst_mem_FP
  have HI : UnaryFn (fun z : List Bool=>(pairSnd z).length) := UnaryFn.length pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_comp (f:=pairFst) (g:=oldCandidate) pairFst_mem_FP oldCandidate_FP) (BinaryFn.ofUnary (HN.sub HI)).bits_mem_FP

noncomputable def degree (z : List Bool) := (IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).degree (boundContext n z)
theorem degree_binary : BinaryFn (degree hn ht ha):=
  (IntegralMixedAuxiliaryCandidateCoordinate.native_access hn ht ha).degree.comp (boundContext_FP hn)

def probeDatum (z : List Bool) := pair (oldCandidate (pairFst (pairFst z)))
  (pair (BinaryNatCode.encode (pairSnd (pairFst z)).length) (pairSnd z))
theorem probeDatum_FP : probeDatum∈FP := by
  have HH : (fun z=>pairFst (pairFst z))∈FP:=mem_FP_comp (f:=pairFst) (g:=pairFst) pairFst_mem_FP pairFst_mem_FP
  have HI : UnaryFn (fun z : List Bool=>(pairSnd (pairFst z)).length):=UnaryFn.length
    (mem_FP_comp (f:=pairFst) (g:=pairSnd) pairFst_mem_FP pairSnd_mem_FP)
  exact mem_FP_pair (mem_FP_comp (f:=fun z=>pairFst (pairFst z)) (g:=oldCandidate) HH oldCandidate_FP)
    (mem_FP_pair (BinaryFn.ofUnary HI).bits_mem_FP pairSnd_mem_FP)

noncomputable def oldProbe (z : List Bool) : List Bool := pair
  (IntegralMixedAuxiliaryCandidate.packet hn ht ha (oldCandidate (pairFst (pairFst z)))) (probeDatum z)
def newProbe (z : List Bool) := pair
  (pair (target (pairFst (pairFst z))) (word (pairFst (pairFst z)))) (probeDatum z)

attribute [local irreducible] IntegralMixedAuxiliaryCandidate.packet

theorem oldProbe_FP : oldProbe hn ht ha∈FP := by
  have HH : (fun z=>pairFst (pairFst z))∈FP:=mem_FP_comp (f:=pairFst) (g:=pairFst) pairFst_mem_FP pairFst_mem_FP
  have HP : (fun z=>oldCandidate (pairFst (pairFst z)))∈FP:=mem_FP_comp (f:=fun z=>pairFst (pairFst z)) (g:=oldCandidate) HH oldCandidate_FP
  have HV : (fun z=>IntegralMixedAuxiliaryCandidate.packet hn ht ha (oldCandidate (pairFst (pairFst z))))∈FP:=
    mem_FP_comp (f:=fun z=>oldCandidate (pairFst (pairFst z))) (g:=IntegralMixedAuxiliaryCandidate.packet hn ht ha)
      HP (IntegralMixedAuxiliaryCandidate.packet_FP hn ht ha)
  exact mem_FP_pair HV probeDatum_FP

theorem newProbe_FP : newProbe∈FP := by
  have HH : (fun z=>pairFst (pairFst z))∈FP:=mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  exact mem_FP_pair (mem_FP_pair (mem_FP_comp (f:=fun z=>pairFst (pairFst z)) (g:=target) HH target_FP)
    (mem_FP_comp (f:=fun z=>pairFst (pairFst z)) (g:=word) HH word_FP)) probeDatum_FP

noncomputable def agrees (q : List Bool) : Prop :=
  ∀ i<dimension n q,∀ k<degree hn ht ha (pair q (List.replicate i true))+1,
    IntegralMixedCandidateReplayOld.value hn ht ha
      (oldProbe hn ht ha (pair (pair q (List.replicate i true)) (BinaryNatCode.encode k)))=
    IntegralFramedPhysicalCandidateReplay.value hn ht ha B
      (newProbe (pair (pair q (List.replicate i true)) (BinaryNatCode.encode k)))

attribute [local irreducible] IntegralMixedCandidateReplayOld.value IntegralFramedPhysicalCandidateReplay.value

theorem scanEvaluator (A : IntegralFramedBankQuery.Access B)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) : SpaceFunction (fun q=>[decide (agrees hn ht ha B q)]) := by
  have EL:=(IntegralMixedCandidateReplayOld.evaluator hn ht ha).precompose (oldProbe hn ht ha) (oldProbe_FP hn ht ha)
  have ER:=(IntegralFramedPhysicalCandidateReplay.evaluator hn ht ha B A T hT hr).precompose newProbe newProbe_FP
  have EC:=(EL.pairOutputs ER).postcompose (fun z=>[decide (pairFst z=pairSnd z)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have ED:=EC.forall_binary ((degree_binary hn ht ha).add (BinaryFn.const 1))
  exact (ED.forall_unary (dimension_unary hn)).congr (funext fun q=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [agrees,Function.comp_apply,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq])

noncomputable def language : Language := {q |
  IntegralMixedAuxiliaryCandidate.Valid hn ht ha (oldCandidate q) ∧
  SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B)
    (target q) (word q) ∧ agrees hn ht ha B q}

theorem decider (A : IntegralFramedBankQuery.Access B)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) : SpaceDecider (language hn ht ha B) := by
  have EO:=((IntegralMixedAuxiliaryCandidate.decider hn ht ha).precompose oldCandidate oldCandidate_FP).flagEvaluator
  have EN:=((SquareSampleCompleteVertices.decider (IntegralFramedPhysicalGridReplay.input_access B A T hT hr)).precompose
    (fun q=>pair (target q) (word q)) (mem_FP_pair target_FP word_FP)).flagEvaluator
  apply (EO.andFlags (EN.andFlags (scanEvaluator hn ht ha B A T hT hr))).decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,IntegralMixedAuxiliaryCandidate.language,SquareSampleCompleteVertices.language,
    Set.mem_ofPred_eq,Set.mem_preimage,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq]

private theorem coordinate_nonzero (q : List Bool) (i : ℕ) :
    (IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).polynomial
      (pair (oldCandidate q) (BinaryNatCode.encode (dimension n q-i)))≠0 := by
  change IntegralMixedFramedCoordinateCharacteristicBits.polynomial
    (IntegralMixedAuxiliaryParameters.parameters (IntegralMixedAuxiliaryPreparedRoot.dimension n) (IntegralMixedAuxiliaryPreparedRoot.term t))
    (IntegralMixedAuxiliaryRecipeRoot.planAt hn ht ha) (IntegralMixedAuxiliaryRecipeRoot.dataAt hn ht ha)
    (IntegralMixedAuxiliaryCandidateCoordinate.sourceContext n t
      (pair (oldCandidate q) (BinaryNatCode.encode (dimension n q-i))))≠0
  exact IntegralMixedFramedCoordinateCharacteristicBits.nonzero _ _ _ _

theorem coordinate_iff (q : List Bool) (hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (oldCandidate q))
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B)
      (target q) (word q)) (i : Fin (dimension n q)) :
    (∀ k<degree hn ht ha (pair q (List.replicate i.val true))+1,
      IntegralMixedCandidateReplayOld.value hn ht ha
        (oldProbe hn ht ha (pair (pair q (List.replicate i.val true)) (BinaryNatCode.encode k)))=
      IntegralFramedPhysicalCandidateReplay.value hn ht ha B
        (newProbe (pair (pair q (List.replicate i.val true)) (BinaryNatCode.encode k)))) ↔
      IntegralMixedAuxiliaryCandidate.point hn ht ha (oldCandidate q) hp i=
        IntegralFramedPhysicalCandidateReplay.point (n:=n) B (context q) (target q) (word q) hv i := by
  have HL (k : ℕ) := IntegralMixedCandidateReplayOld.packet hn ht ha (oldCandidate q) hp i k
  have HR (k : ℕ) := IntegralFramedPhysicalCandidateReplay.packet hn ht ha B (context q) (target q) (word q) hv i k
  have HLeft (k : ℕ) : IntegralMixedCandidateReplayOld.value hn ht ha
      (oldProbe hn ht ha (pair (pair q (List.replicate i.val true)) (BinaryNatCode.encode k)))=
      InfinitesimalSign.encode (ThomEncoding.sign
        (((IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).polynomial
          (pair (oldCandidate q) (BinaryNatCode.encode (dimension n q-i.val)))).map (Int.castRingHom ℝ))
        (IntegralMixedAuxiliaryCandidate.point hn ht ha (oldCandidate q) hp i) k) := by
    simpa only [oldProbe,probeDatum,IntegralMixedCandidateReplayDatum.packet,pairFst_pair,pairSnd_pair,List.length_replicate,dimension] using HL k
  have HRight (k : ℕ) : IntegralFramedPhysicalCandidateReplay.value hn ht ha B
      (newProbe (pair (pair q (List.replicate i.val true)) (BinaryNatCode.encode k)))=
      InfinitesimalSign.encode (ThomEncoding.sign
        (((IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).polynomial
          (pair (oldCandidate q) (BinaryNatCode.encode (dimension n q-i.val)))).map (Int.castRingHom ℝ))
        (IntegralFramedPhysicalCandidateReplay.point (n:=n) B (context q) (target q) (word q) hv i) k) := by
    simpa only [newProbe,probeDatum,IntegralMixedCandidateReplayDatum.packet,pairFst_pair,pairSnd_pair,List.length_replicate,dimension,oldCandidate] using HR k
  simp_rw [HLeft,HRight,SquareSampleTestSign.encode_eq_iff]
  let p:=((IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).polynomial
    (pair (oldCandidate q) (BinaryNatCode.encode (dimension n q-i.val)))).map (Int.castRingHom ℝ)
  let a:=IntegralMixedAuxiliaryCandidate.point hn ht ha (oldCandidate q) hp i
  let b:=IntegralFramedPhysicalCandidateReplay.point (n:=n) B (context q) (target q) (word q) hv i
  have HA : p.eval a=0 := by
    rw [Polynomial.eval_map]
    exact IntegralMixedAuxiliaryCandidateCoordinate.point_root hn ht ha (oldCandidate q) hp i
  have HD : p.natDegree≤degree hn ht ha (pair q (List.replicate i.val true)) := by
    change (Polynomial.map _ _).natDegree≤_
    apply Polynomial.natDegree_map_le.trans
    simpa only [degree,boundContext,pairFst_pair,pairSnd_pair,List.length_replicate] using
      (IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).degree_bound
        (pair (oldCandidate q) (BinaryNatCode.encode (dimension n q-i.val)))
  constructor
  · intro hs
    have HB : SignType.sign (p.eval b)=0 := by
      have H0:=hs 0 (by omega)
      change ThomEncoding.sign p a 0=ThomEncoding.sign p b 0 at H0
      simpa only [ThomEncoding.sign,Function.iterate_zero_apply,HA,sign_zero] using H0.symm
    exact ThomEncoding.root_eq p ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr
      (coordinate_nonzero hn ht ha q i.val)) _ HD a b HA (sign_eq_zero_iff.mp HB) (fun k hk=>hs k (by omega))
  · intro he k _
    rw [he]

theorem language_iff_coordinates (q : List Bool)
    (hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (oldCandidate q))
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B)
      (target q) (word q)) :
    q∈language hn ht ha B ↔ ∀ i : Fin (dimension n q),
      IntegralMixedAuxiliaryCandidate.point hn ht ha (oldCandidate q) hp i=
        IntegralFramedPhysicalCandidateReplay.point (n:=n) B (context q) (target q) (word q) hv i := by
  simp only [language,Set.mem_ofPred_eq,hp,hv,true_and,agrees]
  constructor
  · intro H i
    exact (coordinate_iff hn ht ha B q hp hv i).mp (H i.val i.isLt)
  · intro H i hi
    exact (coordinate_iff hn ht ha B q hp hv ⟨i,hi⟩).mpr (H ⟨i,hi⟩)

theorem language_iff (q : List Bool) : q∈language hn ht ha B ↔
    ∃ hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (oldCandidate q),
      ∃ hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B)
        (target q) (word q),
        ∀ i : Fin (dimension n q),IntegralMixedAuxiliaryCandidate.point hn ht ha (oldCandidate q) hp i=
          IntegralFramedPhysicalCandidateReplay.point (n:=n) B (context q) (target q) (word q) hv i := by
  constructor
  · intro H
    obtain ⟨hp,hv,HG⟩:=H
    exact ⟨hp,hv,(language_iff_coordinates hn ht ha B q hp hv).mp ⟨hp,hv,HG⟩⟩
  · rintro ⟨hp,hv,HE⟩
    exact (language_iff_coordinates hn ht ha B q hp hv).mpr HE

theorem mem_PSPACE (A : IntegralFramedBankQuery.Access B)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) :
    language hn ht ha B∈PSPACE := (decider hn ht ha B A T hT hr).mem_PSPACE

end LeanCanny.Encoding.IntegralFramedPhysicalCandidateReplayThom
