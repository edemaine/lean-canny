/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutLocalInterpretation
/-! # Coefficient-only guards for a reserved virtual interval probe

The final nonzero constant head removes only the endpoint root requirement.
Lower-choice, selected leading and higher-coefficient tests are unchanged.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientOnly
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank native tables represents)
open IntegralMixedPhysicalCutOpenInterval (parent degree Bounds)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
 (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

def head (_ : List Bool):=InfinitesimalSign.encode 1
noncomputable abbrev Guards (z : List Bool):=FiniteCoefficientSignScan.Guards
 (IntegralMixedPhysicalCutLocalGuards.sign hn ht ha hR outer) head
 (IntegralMixedPhysicalCutLocalGuards.choice hn ht ha hR outer)
 (degree hn ht ha hR outer∘pairFst) (IntegralMixedPhysicalCutLocalGuards.cap (bank hn ht ha hR outer).parameters) z

theorem evaluator : SpaceFunction (fun z=>[decide (Guards hn ht ha hR outer z)]):=by
 have ES:=(IntegralMixedPhysicalTraceCutTest.evaluator hn ht ha hR outer
   (IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha hR outer)).precompose
     IntegralMixedPhysicalCutLocalGuards.signQuery IntegralMixedPhysicalCutLocalGuards.signQuery_FP
 have EH : SpaceFunction head:=SpaceFunction.ofFP _ (constFn_mem_FP _)
 exact FiniteCoefficientSignScan.evaluator _ _ _ _ _ ES EH
   (IntegralMixedPhysicalCutLocalGuards.choice_binary hn ht ha hR outer)
   ((IntegralMixedPhysicalCutOpenInterval.degree_binary hn ht ha hR outer).comp pairFst_mem_FP)
   ((BinaryFn.const 2).powUnary ((native hn ht ha hR outer).parameters.width.comp
     (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)))

end LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientOnly
