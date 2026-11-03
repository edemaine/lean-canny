/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedTest
public import LeanCanny.Encoding.IntegralMixedCandidateReplayDatum
public import LeanCanny.Encoding.IntegralFramedPhysicalUnivariateSpace
public import LeanCanny.Algebra.ThomEncoding

/-! # Old candidate derivatives at one full physical marked replay -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalReplayNew
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native represents)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

noncomputable def count (c : List Bool) :=
  (IntegralMixedFramedBankSnapshotBits.atKey (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
    (bank hn ht ha hR outer).data ((bank hn ht ha hR outer).key c)).count

noncomputable def coordinate (c d : List Bool) :
    Fin ((family (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
      (bank hn ht ha hR outer).data).birth ((bank hn ht ha hR outer).key c)) :=
  ⟨count hn ht ha hR outer c-1-IntegralMixedCandidateReplayDatum.index d,by
    have HP:=(bank hn ht ha hR outer).positive c
    change 0<count hn ht ha hR outer c at HP
    change _<count hn ht ha hR outer c
    omega⟩

theorem count_unary : UnaryFn (count hn ht ha hR outer) :=
  (IntegralMixedFramedBankSnapshotBits.count_unary (bank hn ht ha hR outer).parameters
    (native hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data).comp
    (native hn ht ha hR outer).key

theorem coordinate_unary : UnaryFn (IntegralFramedPhysicalUnivariateTest.selected
    (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
      (bank hn ht ha hR outer).key (coordinate hn ht ha hR outer)) := by
  have HC:=(count_unary hn ht ha hR outer).comp pairFst_mem_FP
  have HI : BinaryFn (fun z=>IntegralMixedCandidateReplayDatum.index (pairSnd z)) :=
    BinaryFn.fromBits (mem_FP_comp (f:=pairSnd) (g:=fun d=>pairFst (pairSnd d)) pairSnd_mem_FP
      (mem_FP_comp (f:=pairSnd) (g:=pairFst) pairSnd_mem_FP pairFst_mem_FP))
  have HB : BinaryFn (IntegralFramedPhysicalUnivariateTest.selected
      (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
        (bank hn ht ha hR outer).key (coordinate hn ht ha hR outer)) :=
    ((BinaryFn.ofUnary HC).sub (BinaryFn.const 1)).sub HI
  exact IntegralMixedDenominatorScriptBits.binary_bounded_unary HB HC (fun _=>by
    change _-1-_≤_
    omega)

noncomputable def value :=IntegralFramedPhysicalUnivariateTest.value
  (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
  (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed
  (bank hn ht ha hR outer).bounds (bank hn ht ha hR outer).key (bank hn ht ha hR outer).positive
  (coordinate hn ht ha hR outer) (IntegralMixedCandidateReplayDatum.source hn ht ha)

attribute [local irreducible] bank coordinate

theorem evaluator (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha hR outer))) :
    SpaceFunction (value hn ht ha hR outer) := by
  let A:=native hn ht ha hR outer
  exact IntegralFramedPhysicalUnivariateTest.evaluator
    (bank hn ht ha hR outer).parameters A.parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
    (tables hn ht ha hR outer) (tables_native hn ht ha hR outer) (represents hn ht ha hR outer)
    (bank hn ht ha hR outer).key A.key (coordinate hn ht ha hR outer) (coordinate_unary hn ht ha hR outer)
    A.liftedData A.controls A.bounds A.nodes A.factor A.seed (bank hn ht ha hR outer).bounds
    (IntegralMixedCandidateReplayDatum.source hn ht ha) (IntegralMixedCandidateReplayDatum.access hn ht ha)
    (bank hn ht ha hR outer).positive ER

theorem coordinate_packet (c p : List Bool) (i k : ℕ) :
    (coordinate hn ht ha hR outer c (IntegralMixedCandidateReplayDatum.packet p i k)).val=
      count hn ht ha hR outer c-1-i := by
  unfold coordinate
  simp only [IntegralMixedCandidateReplayDatum.index,IntegralMixedCandidateReplayDatum.packet,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

noncomputable def point (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w) :
    Fin (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx)→ℝ := fun i=>
  IntegralFramedPhysicalSquare.point (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
    (bank hn ht ha hR outer).data (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor
    (bank hn ht ha hR outer).seed (bank hn ht ha hR outer).bounds
    (bank hn ht ha hR outer).key (bank hn ht ha hR outer).positive (sampleContext ctx) w hv
    (coordinate hn ht ha hR outer (sampleContext ctx) (IntegralMixedCandidateReplayDatum.packet (pairFst ctx) i.val 0))

theorem packet (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w)
    (i : Fin (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx)) (k : ℕ) :
    value hn ht ha hR outer (pair (pair (sampleContext ctx) w) (IntegralMixedCandidateReplayDatum.packet (pairFst ctx) i.val k))=
      InfinitesimalSign.encode (ThomEncoding.sign
        (((IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).polynomial
          (pair (pairFst ctx) (BinaryNatCode.encode (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx-i.val)))).map
          (Int.castRingHom ℝ)) (point hn ht ha hR outer ctx w hv i) k) := by
  have HC : coordinate hn ht ha hR outer (sampleContext ctx) (IntegralMixedCandidateReplayDatum.packet (pairFst ctx) i.val k)=
      coordinate hn ht ha hR outer (sampleContext ctx) (IntegralMixedCandidateReplayDatum.packet (pairFst ctx) i.val 0) :=by
    apply Fin.ext
    rw [coordinate_packet,coordinate_packet]
  have HP:=IntegralFramedPhysicalUnivariateTest.packet
    (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
    (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed
    (bank hn ht ha hR outer).bounds (bank hn ht ha hR outer).key (bank hn ht ha hR outer).positive
    (coordinate hn ht ha hR outer) (IntegralMixedCandidateReplayDatum.source hn ht ha)
    (sampleContext ctx) w (IntegralMixedCandidateReplayDatum.packet (pairFst ctx) i.val k) hv
  rw [IntegralMixedCandidateReplayDatum.polynomial_packet,HC] at HP
  simpa only [value,point,IntegralMixedAuxiliaryMarkedIntegerSource.number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,ThomEncoding.sign,Polynomial.iterate_derivative_map,Polynomial.eval_map] using HP

end LeanCanny.Encoding.IntegralMixedPhysicalReplayNew
