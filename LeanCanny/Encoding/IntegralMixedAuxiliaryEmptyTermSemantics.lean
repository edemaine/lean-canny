/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankTermObservation
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateTermInput
/-! # Original-only term replies at a bank-only observation of one joint root -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters
open scoped Classical
variable {n : List Bool→ℕ} {t : List Bool→Term}

noncomputable def termPoint (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP)
    (ha : ∀ q,(t q).arity≤n q) (key : List Bool→List Bool)
    (hpos : ∀ c,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key c))
    (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (termSampleInput hn ht ha key hpos) c w) : ℕ→ℝ :=
  IntegralFramedBankTermTest.observedPoint (parameters n t) (plan hn ht ha) (data hn ht ha) (key c)
    (IntegralMixedFramedBankObservation.extend
      (SquareSampleCompleteVertices.candidate (termSampleInput hn ht ha key hpos) c w hv).val)

theorem term_packet (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP)
    (ha : ∀ q,(t q).arity≤n q) (key : List Bool→List Bool)
    (hpos : ∀ c,0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key c))
    (word : List Bool→List Bool) (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (termSampleInput hn ht ha key hpos) c w) :
    termValue hn ht ha key hpos word (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign (((IntegralMixedFramedBankTermBits.source word).syntax (key c)).eval
        (termPoint hn ht ha key hpos c w hv))) :=
  IntegralFramedBankTermTest.packet_observation (parameters n t) (plan hn ht ha) (data hn ht ha)
    (termSyntax hn ht ha) (familyInputs hn ht ha) key _ word c w d hv

end LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
