/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutValidity
public import LeanCanny.Encoding.IntegralFramedPhysicalBankObservation

/-! # A full cut's native zero guard reads its actual raw scalar column -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientSemantics
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank tables represents)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] bank tables SquareSampleCompleteCoordinateSign.value
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
  (ctx w u : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w)

theorem head_packet
    (hfit : u.length<IntegralMixedPhysicalReplayNew.count hn ht ha hR outer (sampleContext ctx)) :
    IntegralMixedPhysicalTraceCutGuards.head hn ht ha hR outer (stage ctx w u)=InfinitesimalSign.encode
      (SignType.sign (IntegralFramedPhysicalSuffixTest.rawTuple (bank hn ht ha hR outer)
        (sampleContext ctx) w hv
          (IntegralMixedPhysicalReplayNew.count hn ht ha hR outer (sampleContext ctx)-u.length-1))) :=by
  let m:=IntegralMixedPhysicalReplayNew.count hn ht ha hR outer (sampleContext ctx)
  let i : Fin ((IntegralFramedBankQuery.input (bank hn ht ha hR outer)).count (sampleContext ctx)) :=
    ⟨m-u.length-1,by change m-u.length-1<m;change u.length<m at hfit;omega⟩
  have HP:=IntegralFramedPhysicalSuffixTest.scalar_column_sign (bank hn ht ha hR outer)
    (sampleContext ctx) w hv (tables hn ht ha hR outer) (represents hn ht ha hR outer) i
  simpa only [IntegralMixedPhysicalTraceCutGuards.head,Function.comp_apply,
    IntegralMixedPhysicalTraceCutGuards.headQuery,IntegralMixedPhysicalTraceCutGuards.sample,
    IntegralMixedPhysicalTraceCutGuards.column,IntegralMixedPhysicalTraceCutGuards.age,
    IntegralFramedTraceCutGuards.root,IntegralFramedTraceCutGuards.word,IntegralFramedTraceCutGuards.stage,
    stage,pairFst_pair,pairSnd_pair,i,m] using HP

theorem head_zero_iff
    (hfit : u.length<IntegralMixedPhysicalReplayNew.count hn ht ha hR outer (sampleContext ctx)) :
    IntegralMixedPhysicalTraceCutGuards.head hn ht ha hR outer (stage ctx w u)=InfinitesimalSign.encode 0 ↔
      IntegralFramedPhysicalSuffixTest.rawTuple (bank hn ht ha hR outer) (sampleContext ctx) w hv
        (IntegralMixedPhysicalReplayNew.count hn ht ha hR outer (sampleContext ctx)-u.length-1)=0 :=by
  rw [head_packet hn ht ha hR outer ctx w u hv hfit]
  exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff

end LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientSemantics
