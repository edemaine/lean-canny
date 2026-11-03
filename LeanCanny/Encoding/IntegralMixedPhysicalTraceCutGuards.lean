/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutTest
public import LeanCanny.Encoding.IntegralMixedPhysicalReplayThom
public import LeanCanny.Encoding.IntegralFramedTraceCutGuards

/-! # Native cut guards preserve the full marked context and word -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalTraceCutGuards
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native controls)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open IntegralFramedTraceCutGuards (root word stage root_FP word_FP stage_unary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

def query (z : List Bool) :=pair
  (pair (sampleContext (root (pairFst z))) (word (pairFst z)))
  (pair (pairSnd (pairFst z)) (pairSnd z))
theorem query_FP : query∈FP :=by
  have HR:=mem_FP_comp (mem_FP_comp pairFst_mem_FP root_FP) IntegralMixedPhysicalMarkedTest.sampleContext_FP
  have HW:=mem_FP_comp pairFst_mem_FP word_FP
  exact mem_FP_pair (mem_FP_pair HR HW)
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)

noncomputable def age (b : List Bool) :=
  IntegralMixedPhysicalReplayNew.count hn ht ha hR outer (sampleContext (root b))-stage b-1
noncomputable def column (b : List Bool) :=
  IntegralMixedFramedPhysicalIndex.scalarColumn (bank hn ht ha hR outer).parameters (tables hn ht ha hR outer)
    (pair ((bank hn ht ha hR outer).key (sampleContext (root b))) (BinaryNatCode.encode (age hn ht ha hR outer b)))

theorem age_unary : UnaryFn (age hn ht ha hR outer) :=
  (((IntegralMixedPhysicalReplayNew.count_unary hn ht ha hR outer).comp
    (mem_FP_comp root_FP IntegralMixedPhysicalMarkedTest.sampleContext_FP)).sub stage_unary).sub (UnaryFn.const 1)

theorem column_unary : UnaryFn (column hn ht ha hR outer) :=by
  let B:=bank hn ht ha hR outer
  let A:=native hn ht ha hR outer
  exact (IntegralMixedFramedPhysicalIndex.scalarColumn_unary B.parameters A.parameters
    (tables hn ht ha hR outer) (tables_native hn ht ha hR outer)).comp
      (mem_FP_pair (mem_FP_comp (mem_FP_comp root_FP IntegralMixedPhysicalMarkedTest.sampleContext_FP) A.key)
        (BinaryFn.ofUnary (age_unary hn ht ha hR outer)).bits_mem_FP)

def sample (b : List Bool) :=pair (sampleContext (root b)) (word b)
theorem sample_FP : sample∈FP :=
  mem_FP_pair (mem_FP_comp root_FP IntegralMixedPhysicalMarkedTest.sampleContext_FP) word_FP
noncomputable def headQuery (b : List Bool) :=pair (sample b) (BinaryNatCode.encode (column hn ht ha hR outer b))
theorem headQuery_FP : headQuery hn ht ha hR outer∈FP :=
  mem_FP_pair sample_FP (BinaryFn.ofUnary (column_unary hn ht ha hR outer)).bits_mem_FP

noncomputable def sign :=IntegralMixedPhysicalTraceCutTest.value hn ht ha hR outer∘query
noncomputable def head :=SquareSampleCompleteCoordinateSign.value (input hn ht ha hR outer)∘headQuery hn ht ha hR outer
noncomputable abbrev Guards (b : List Bool) : Prop :=FiniteCoefficientSignScan.Guards
  (sign hn ht ha hR outer) (head hn ht ha hR outer)
  (IntegralFramedTraceCutGuards.choice (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data)
  (IntegralFramedTraceCutGuards.degree (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data)
  (IntegralFramedTraceCutGuards.cap (bank hn ht ha hR outer).parameters) b

attribute [local irreducible] bank tables sign head column age IntegralMixedPhysicalTraceCutTest.value

theorem evaluator (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha hR outer))) :
    SpaceFunction (fun b=>[decide (Guards hn ht ha hR outer b)]) :=by
  let B:=bank hn ht ha hR outer
  let A:=native hn ht ha hR outer
  let C:=(controls hn ht ha hR outer).normalization
  have ES : SpaceFunction (sign hn ht ha hR outer):=by
    unfold sign
    exact (IntegralMixedPhysicalTraceCutTest.evaluator hn ht ha hR outer ER).precompose query query_FP
  have EH : SpaceFunction (head hn ht ha hR outer):=by
    unfold head
    exact (SquareSampleCompleteCoordinateSign.evaluator
      (IntegralMixedPhysicalReplayThom.input_access hn ht ha hR outer ER)).precompose
        (headQuery hn ht ha hR outer) (headQuery_FP hn ht ha hR outer)
  exact FiniteCoefficientSignScan.evaluator _ _ _ _ _ ES EH
    (IntegralFramedTraceCutGuards.choice_binary B.parameters A.parameters B.plan B.data C)
    (IntegralFramedTraceCutGuards.degree_binary B.parameters A.parameters B.plan B.data C)
    (IntegralFramedTraceCutGuards.cap_binary B.parameters A.parameters)

end LeanCanny.Encoding.IntegralMixedPhysicalTraceCutGuards
