/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedPreludePrefix
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordPlan
/-! # The actual marked prelude has the constructed original leaf order

The range is reversed because both framed command lists and the symbolic
recursion store the newest birth first. Polynomial values remain native.
-/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedPreludeActual
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem reverse_range_map {α:Type*} (f:ℕ→α) (N:ℕ):
    (List.range N).reverse.map f=List.ofFn (fun i:Fin N=>f (N-1-i.val)):=by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_reverse,List.length_range,List.length_ofFn]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_reverse,List.length_range,List.getElem_range,List.getElem_ofFn]

variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

def indices (n:List Bool→ℕ) (ctx:List Bool):List ℕ:=
  (List.range (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8)).reverse

theorem indices_length (ctx:List Bool):
    (indices n ctx).length=IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8:=by
  simp only [indices,List.length_reverse,List.length_range]

/-- Literal equality to the existing original marked integer-plan commands. -/
theorem commands_eq (ctx:List Bool) (radius:List Bool→ℕ):
    CoefficientMarkedPreludePrefix.commands hn ht ha ctx radius (indices n ctx)=
      (IntegralMixedAuxiliaryMarkedIntegerPlan.plan hn ht ha radius).rules ctx:=by
  rw [CoefficientMarkedPreludePrefix.commands,indices,reverse_range_map]
  change List.ofFn (fun i:Fin (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8)=>
      CoefficientMarkedPreludePrefix.instruction hn ht ha ctx radius
        (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8-1-i.val))=
    List.ofFn _
  congr 1

/-- The same commands are the literal oldest suffix of the full record plan. -/
theorem record_suffix (ctx:List Bool) (radius:List Bool→ℕ):
    ((IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius).rules ctx).drop
      (IntegralMixedCausalRecordPlanBits.count ctx)=
      CoefficientMarkedPreludePrefix.commands hn ht ha ctx radius (indices n ctx):=by
  rw [commands_eq hn ht ha ctx radius]
  let A:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let S:∀root,ℕ→SpatialSource (A.ambient root):=fun root _=>
    IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t radius root
  let N:=fun root=>IntegralMixedAuxiliaryMarkedIntegerSource.number n root+8
  let raw:=IntegralMixedSourceIntegerRecordAppend.later A S
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t radius root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.spatial_cap hn ht ha) N
  have HR:∀root,(raw root).length+N root+2≤A.cap root+1:=by
    intro root
    rw [IntegralMixedSourceIntegerRecordAppend.later_length]
    exact IntegralMixedAuxiliaryMarkedRecordPlan.room hn ht ha root
  have H:=IntegralMixedSourceIntegerPrelude.extended_suffix A (fun root=>S root 0)
    (fun root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t radius root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.spatial_cap hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha radius) N
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha radius)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha radius) raw HR ctx
  change ((IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius).rules ctx).drop
      (raw ctx).length=(IntegralMixedAuxiliaryMarkedIntegerPlan.plan hn ht ha radius).rules ctx at H
  rw [IntegralMixedSourceIntegerRecordAppend.later_length] at H
  exact H

end LeanCanny.Encoding.CoefficientMarkedPreludeActual
