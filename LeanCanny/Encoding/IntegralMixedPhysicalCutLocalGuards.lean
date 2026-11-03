/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutOpenInterval
public import LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientSemantics
/-! # Original cut guards retain their exact full sampling context

Unlike the older normalized-context frontend, every coefficient and head
query below retains q and its ONE full word. Only polynomial metadata changes.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutLocalGuards
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank native controls tables tables_native represents)
open IntegralMixedPhysicalCutOpenInterval (birthWord parent count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] bank native controls tables IntegralMixedFramedHistoryFamilyBits.family
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

def signQuery (r : List Bool) :=pair (pairFst r)
  (pair (birthWord (pairFst (pairFst r))) (pairSnd r))
theorem signQuery_FP : signQuery∈FP :=by polytime [signQuery,birthWord]
noncomputable def sign :=IntegralMixedPhysicalTraceCutTest.value hn ht ha hR outer∘signQuery

noncomputable def age (z : List Bool) :=count hn ht ha hR outer (pairFst z)-(birthWord (pairFst z)).length-1
theorem age_unary : UnaryFn (age hn ht ha hR outer) :=
  (((IntegralMixedPhysicalCutOpenInterval.count_unary hn ht ha hR outer).comp pairFst_mem_FP).sub
    (UnaryFn.length (by polytime [birthWord]))).sub (UnaryFn.const 1)
noncomputable def column (z : List Bool) :=IntegralMixedFramedPhysicalIndex.scalarColumn
  (bank hn ht ha hR outer).parameters (tables hn ht ha hR outer)
  (pair ((bank hn ht ha hR outer).key (pairFst z)) (BinaryNatCode.encode (age hn ht ha hR outer z)))
theorem column_unary : UnaryFn (column hn ht ha hR outer) :=
  (IntegralMixedFramedPhysicalIndex.scalarColumn_unary (bank hn ht ha hR outer).parameters
    (native hn ht ha hR outer).parameters (tables hn ht ha hR outer) (tables_native hn ht ha hR outer)).comp
      (mem_FP_pair (mem_FP_comp pairFst_mem_FP (native hn ht ha hR outer).key)
        (BinaryFn.ofUnary (age_unary hn ht ha hR outer)).bits_mem_FP)
noncomputable def headQuery (z : List Bool) :=pair z (BinaryNatCode.encode (column hn ht ha hR outer z))
theorem headQuery_FP : headQuery hn ht ha hR outer∈FP :=
  mem_FP_pair id_mem_FP (BinaryFn.ofUnary (column_unary hn ht ha hR outer)).bits_mem_FP
noncomputable def head :=SquareSampleCompleteCoordinateSign.value
  (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer)∘headQuery hn ht ha hR outer

noncomputable def choice (z : List Bool) :=IntegralFramedTraceCutGuards.choice
  (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
  (IntegralMixedPhysicalCutOpenInterval.guardContext (pairFst z))
theorem choice_binary : BinaryFn (choice hn ht ha hR outer) :=by
  let B:=bank hn ht ha hR outer
  let A:=native hn ht ha hR outer
  have HC : BinaryFn (IntegralFramedTraceCutGuards.choice B.parameters B.plan B.data) :=
    IntegralFramedTraceCutGuards.choice_binary B.parameters A.parameters B.plan B.data
      (controls hn ht ha hR outer).normalization
  exact HC.comp (mem_FP_comp pairFst_mem_FP IntegralMixedPhysicalCutOpenInterval.guardContext_FP)
def cap (P : Parameters) (z : List Bool) :=2^P.width (pairFst (pairFst z))

noncomputable abbrev Guards (z : List Bool) :=FiniteCoefficientSignScan.Guards
  (sign hn ht ha hR outer) (head hn ht ha hR outer) (choice hn ht ha hR outer)
  (IntegralMixedPhysicalCutOpenInterval.degree hn ht ha hR outer∘pairFst) (cap (bank hn ht ha hR outer).parameters) z

attribute [local irreducible] sign head choice column age

theorem evaluator : SpaceFunction (fun z=>[decide (Guards hn ht ha hR outer z)]) :=by
  have ES : SpaceFunction (sign hn ht ha hR outer) :=by
    unfold sign
    exact (IntegralMixedPhysicalTraceCutTest.evaluator hn ht ha hR outer
      (IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha hR outer)).precompose signQuery signQuery_FP
  have EH : SpaceFunction (head hn ht ha hR outer) :=by
    unfold head
    exact (SquareSampleCompleteCoordinateSign.evaluator
      (IntegralMixedPhysicalMarkedNative.access hn ht ha hR outer)).precompose
        (headQuery hn ht ha hR outer) (headQuery_FP hn ht ha hR outer)
  have HD : BinaryFn (IntegralMixedPhysicalCutOpenInterval.degree hn ht ha hR outer∘pairFst) :=
    (IntegralMixedPhysicalCutOpenInterval.degree_binary hn ht ha hR outer).comp pairFst_mem_FP
  have HC : BinaryFn (cap (bank hn ht ha hR outer).parameters) :=
    (BinaryFn.const 2).powUnary ((native hn ht ha hR outer).parameters.width.comp
      (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))
  exact FiniteCoefficientSignScan.evaluator _ _ _ _ _ ES EH
    (choice_binary hn ht ha hR outer) HD HC

theorem sign_packet (q w : List Bool) (e k : ℕ) :
    sign hn ht ha hR outer (FiniteCoefficientSignScan.query (pair q w) e k)=
      IntegralMixedPhysicalTraceCutTest.value hn ht ha hR outer
        (pair (pair q w) (IntegralFramedPhysicalTraceCutSource.datum (birthWord q) e k)) :=by
  simp only [sign,Function.comp_apply,signQuery,FiniteCoefficientSignScan.query,
    IntegralFramedPhysicalTraceCutSource.datum,pairFst_pair,pairSnd_pair]

end LeanCanny.Encoding.IntegralMixedPhysicalCutLocalGuards
