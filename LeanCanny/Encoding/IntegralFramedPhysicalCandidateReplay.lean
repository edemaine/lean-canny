/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalGridReplay
public import LeanCanny.Encoding.IntegralMixedCandidateReplayDatum
public import LeanCanny.Encoding.IntegralFramedPhysicalUnivariateSpace
public import LeanCanny.Algebra.ThomEncoding

/-! # Old candidate derivatives at one full physical marked replay -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalCandidateReplay
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  (B : Bank)

noncomputable def count (c : List Bool) :=
  (IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan
    B.data (B.key c)).count

noncomputable def coordinate (c d : List Bool) :
    Fin ((family B.parameters B.plan
      B.data).birth (B.key c)) :=
  ⟨count B c-1-IntegralMixedCandidateReplayDatum.index d,by
    have HP:=B.positive c
    change 0<count B c at HP
    change _<count B c
    omega⟩

theorem count_unary (A : IntegralFramedBankQuery.Access B) : UnaryFn (count B) :=
  (IntegralMixedFramedBankSnapshotBits.count_unary B.parameters
    A.parameters B.plan B.data).comp
    A.key

theorem coordinate_unary (A : IntegralFramedBankQuery.Access B) : UnaryFn (IntegralFramedPhysicalUnivariateTest.selected
    B.parameters B.plan B.data
      B.key (coordinate B)) := by
  have HC:=(count_unary B A).comp pairFst_mem_FP
  have HI : BinaryFn (fun z=>IntegralMixedCandidateReplayDatum.index (pairSnd z)) :=
    BinaryFn.fromBits (mem_FP_comp (f:=pairSnd) (g:=fun d=>pairFst (pairSnd d)) pairSnd_mem_FP
      (mem_FP_comp (f:=pairSnd) (g:=pairFst) pairSnd_mem_FP pairFst_mem_FP))
  have HB : BinaryFn (IntegralFramedPhysicalUnivariateTest.selected
      B.parameters B.plan B.data
        B.key (coordinate B)) :=
    ((BinaryFn.ofUnary HC).sub (BinaryFn.const 1)).sub HI
  exact IntegralMixedDenominatorScriptBits.binary_bounded_unary HB HC (fun _=>by
    change _-1-_≤_
    omega)

noncomputable def value :=IntegralFramedPhysicalUnivariateTest.value
  B.parameters B.plan B.data
  B.nodes B.factor B.seed
  B.bounds B.key B.positive
  (coordinate B) (IntegralMixedCandidateReplayDatum.source hn ht ha)

attribute [local irreducible] coordinate

theorem evaluator (A : IntegralFramedBankQuery.Access B)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) :
    SpaceFunction (value hn ht ha B) :=
  IntegralFramedPhysicalUnivariateTest.evaluator B.parameters A.parameters B.plan B.data T hT hr B.key A.key
    (coordinate B) (coordinate_unary B A) A.liftedData A.controls A.bounds A.nodes A.factor A.seed B.bounds
    (IntegralMixedCandidateReplayDatum.source hn ht ha) (IntegralMixedCandidateReplayDatum.access hn ht ha) B.positive
    (IntegralFramedPhysicalSquare.native_row_evaluator B.parameters A.parameters B.plan B.data T hT hr
      B.nodes B.factor B.seed B.bounds B.key A.key B.positive A.liftedData A.controls A.bounds)

theorem coordinate_packet (c p : List Bool) (i k : ℕ) :
    (coordinate B c (IntegralMixedCandidateReplayDatum.packet p i k)).val=
      count B c-1-i := by
  unfold coordinate
  simp only [IntegralMixedCandidateReplayDatum.index,IntegralMixedCandidateReplayDatum.packet,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

noncomputable def point (ctx target w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B) target w) :
    Fin (n (pairFst (pairFst ctx)))→ℝ := fun i=>
  IntegralFramedPhysicalSquare.point B.parameters B.plan
    B.data B.nodes B.factor
    B.seed B.bounds
    B.key B.positive target w hv
    (coordinate B target (IntegralMixedCandidateReplayDatum.packet (pairFst ctx) i.val 0))

theorem packet (ctx target w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B) target w)
    (i : Fin (n (pairFst (pairFst ctx)))) (k : ℕ) :
    value hn ht ha B (pair (pair target w) (IntegralMixedCandidateReplayDatum.packet (pairFst ctx) i.val k))=
      InfinitesimalSign.encode (ThomEncoding.sign
        (((IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).polynomial
          (pair (pairFst ctx) (BinaryNatCode.encode (n (pairFst (pairFst ctx))-i.val)))).map
          (Int.castRingHom ℝ)) (point (n:=n) B ctx target w hv i) k) := by
  have HC : coordinate B target (IntegralMixedCandidateReplayDatum.packet (pairFst ctx) i.val k)=
      coordinate B target (IntegralMixedCandidateReplayDatum.packet (pairFst ctx) i.val 0) :=by
    apply Fin.ext
    rw [coordinate_packet,coordinate_packet]
  have HP:=IntegralFramedPhysicalUnivariateTest.packet
    B.parameters B.plan B.data
    B.nodes B.factor B.seed
    B.bounds B.key B.positive
    (coordinate B) (IntegralMixedCandidateReplayDatum.source hn ht ha)
    target w (IntegralMixedCandidateReplayDatum.packet (pairFst ctx) i.val k) hv
  rw [IntegralMixedCandidateReplayDatum.polynomial_packet,HC] at HP
  simpa only [value,point,ThomEncoding.sign,Polynomial.iterate_derivative_map,Polynomial.eval_map] using HP

end LeanCanny.Encoding.IntegralFramedPhysicalCandidateReplay
