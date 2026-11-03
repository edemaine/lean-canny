/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCandidateReplayDatum
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerBank
public import LeanCanny.Algebra.ThomEncoding
public import LeanCanny.Algebra.IntegralMixedDenominatorNative
/-! # Shared datum-selected derivatives at one marked replay vertex -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCandidateReplayNew
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)

noncomputable abbrev bank := IntegralMixedAuxiliaryMarkedIntegerPlan.bank hn ht ha hR
noncomputable abbrev input := IntegralFramedBankQuery.input (bank hn ht ha hR)
def sampleContext (context : List Bool) := pair context []
theorem sampleContext_FP : sampleContext∈FP:=mem_FP_pair id_mem_FP (constFn_mem_FP [])

noncomputable def coordinate (c d : List Bool) : Fin ((input hn ht ha hR).count c) :=
  ⟨(input hn ht ha hR).count c-1-IntegralMixedCandidateReplayDatum.index d,by
    have H:=(input hn ht ha hR).count_pos c
    omega⟩

theorem coordinate_unary : UnaryFn ((fun z=>(coordinate hn ht ha hR (pairFst z) (pairSnd z)).val)) := by
  let A:=IntegralMixedAuxiliaryMarkedIntegerPlan.bank_access hn ht ha hR
  have HC : UnaryFn (fun z=>(input hn ht ha hR).count (pairFst z)) :=
    (IntegralMixedFramedBankSnapshotBits.count_unary (bank hn ht ha hR).parameters A.parameters
      (bank hn ht ha hR).plan (bank hn ht ha hR).data).comp
      (mem_FP_comp (f:=pairFst) (g:=(bank hn ht ha hR).key) pairFst_mem_FP A.key)
  have HI : BinaryFn (fun z=>IntegralMixedCandidateReplayDatum.index (pairSnd z)) := BinaryFn.fromBits
    (mem_FP_comp (f:=pairSnd) (g:=fun d=>pairFst (pairSnd d)) pairSnd_mem_FP
      (mem_FP_comp (f:=pairSnd) (g:=pairFst) pairSnd_mem_FP pairFst_mem_FP))
  have HB : BinaryFn ((fun z=>(coordinate hn ht ha hR (pairFst z) (pairSnd z)).val)) :=
    ((BinaryFn.ofUnary HC).sub (BinaryFn.const 1)).sub HI
  exact IntegralMixedDenominatorScriptBits.binary_bounded_unary HB HC (fun z=>by
    change _-1-_≤_
    omega)

noncomputable def value : List Bool→List Bool := IntegralFramedBankUnivariateTest.value (bank hn ht ha hR).parameters (bank hn ht ha hR).plan
  (bank hn ht ha hR).data (bank hn ht ha hR).nodes (bank hn ht ha hR).factor (bank hn ht ha hR).seed
  (bank hn ht ha hR).bounds (bank hn ht ha hR).key (bank hn ht ha hR).positive
  (coordinate hn ht ha hR) (IntegralMixedCandidateReplayDatum.source hn ht ha)

theorem count_eq (c : List Bool) : (input hn ht ha hR).count c=
    IntegralMixedAuxiliaryMarkedIntegerSource.number n (pairFst c)+8 :=
  IntegralMixedAuxiliaryMarkedIntegerPlan.bank_count hn ht ha hR c

attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerPlan.bank coordinate

theorem evaluator : SpaceFunction (value hn ht ha hR) := by
  let A:=IntegralMixedAuxiliaryMarkedIntegerPlan.bank_access hn ht ha hR
  exact IntegralFramedBankUnivariateTest.evaluator _ A.parameters _ _ A.liftedData A.controls A.bounds
    A.nodes A.factor A.seed (bank hn ht ha hR).bounds (bank hn ht ha hR).key A.key (bank hn ht ha hR).positive
    (coordinate hn ht ha hR) (coordinate_unary hn ht ha hR) _ (IntegralMixedCandidateReplayDatum.access hn ht ha)

noncomputable def point (context w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext context) w) :
    Fin (IntegralMixedAuxiliaryMarkedIntegerSource.number n context)→ℝ := fun i=>
  (IntegralMixedFramedBankObservation.ofState (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state
    (bank hn ht ha hR).parameters (bank hn ht ha hR).plan (bank hn ht ha hR).data
    ((bank hn ht ha hR).key (sampleContext context)))).point
    (IntegralMixedFramedBankObservation.extend (SquareSampleCompleteVertices.candidate (input hn ht ha hR)
      (sampleContext context) w hv).val) (IntegralMixedAuxiliaryMarkedIntegerSource.number n context+7-i.val)

theorem packet (context w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext context) w)
    (i : Fin (IntegralMixedAuxiliaryMarkedIntegerSource.number n context)) (k : ℕ) :
    value hn ht ha hR (pair (pair (sampleContext context) w)
      (IntegralMixedCandidateReplayDatum.packet (pairFst context) i.val k))=
      InfinitesimalSign.encode (ThomEncoding.sign
        (((IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).polynomial
          (pair (pairFst context) (BinaryNatCode.encode (IntegralMixedAuxiliaryMarkedIntegerSource.number n context-i.val)))).map
          (Int.castRingHom ℝ)) (point hn ht ha hR context w hv i) k) := by
  have HI : (coordinate hn ht ha hR (sampleContext context)
      (IntegralMixedCandidateReplayDatum.packet (pairFst context) i.val k)).val=
      IntegralMixedAuxiliaryMarkedIntegerSource.number n context+7-i.val := by
    rw [coordinate]
    simp only [IntegralMixedCandidateReplayDatum.index,IntegralMixedCandidateReplayDatum.packet,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    rw [count_eq]
    simp only [sampleContext,pairFst_pair]
    omega
  have HP:=IntegralFramedBankUnivariateTest.packet (bank hn ht ha hR).parameters (bank hn ht ha hR).plan
    (bank hn ht ha hR).data (bank hn ht ha hR).nodes (bank hn ht ha hR).factor (bank hn ht ha hR).seed
    (bank hn ht ha hR).bounds (bank hn ht ha hR).key (bank hn ht ha hR).positive
    (coordinate hn ht ha hR) (IntegralMixedCandidateReplayDatum.source hn ht ha) (sampleContext context) w
    (IntegralMixedCandidateReplayDatum.packet (pairFst context) i.val k) hv
  have HX:=IntegralMixedFramedBankObservation.point_ofState
    (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state (bank hn ht ha hR).parameters (bank hn ht ha hR).plan
      (bank hn ht ha hR).data ((bank hn ht ha hR).key (sampleContext context)))
    (SquareSampleCompleteVertices.candidate (input hn ht ha hR) (sampleContext context) w hv).val
    (coordinate hn ht ha hR (sampleContext context) (IntegralMixedCandidateReplayDatum.packet (pairFst context) i.val k))
  rw [IntegralMixedCandidateReplayDatum.polynomial_packet,←HX,HI] at HP
  simpa only [value,point,IntegralMixedAuxiliaryMarkedIntegerSource.number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,ThomEncoding.sign,Polynomial.iterate_derivative_map,Polynomial.eval_map] using HP

end LeanCanny.Encoding.IntegralMixedCandidateReplayNew
