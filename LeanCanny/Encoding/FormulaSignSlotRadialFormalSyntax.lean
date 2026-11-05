/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialFormalBounds
public import LeanCanny.ETR.TubeZeroSyntax
public import LeanCanny.ETR.FinitePolynomialPadding
/-! # A short original-syntax writer for the full formal radial input -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialFormalInput
open ETR LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def spatial (c :List Bool):=N c+d c+1
noncomputable def dimension (c :List Bool):=spatial c+(d c+1)
def difference (left right :ℕ):Term:=.add (.var left) (.mul (.const (-1)) (.var right))
noncomputable def centerDifference (c :List Bool) (i :ℕ):=difference (N c+i) (spatial c+i)
noncomputable def centerTerms (c :List Bool):=(List.range (d c)).map (centerDifference c)
noncomputable def centerSquares (c :List Bool):=SumSquares.accumulate (centerTerms c) (.const 0)
noncomputable def radiusDifference (c :List Bool):=difference (N c+d c) (spatial c+d c)
noncomputable def equation (c :List Bool):Term:=.add
  (.add (FormulaSignSlotCenteredRadialSource.equation c) (centerSquares c)) (radiusDifference c).square

theorem spatial_unary :UnaryFn spatial:=FormulaSignSlotCenteredRadialSource.dimension_unary
theorem dimension_unary :UnaryFn dimension:=
  spatial_unary.add (FormulaSignSlotSource.dimension_unary.add (UnaryFn.const 1))

private theorem difference_FP {left right :List Bool→ℕ} (hl :UnaryFn left) (hr :UnaryFn right):
    (fun c=>(difference (left c) (right c)).toData.toBits)∈FP:=by
  have HL:(fun c=>(Term.var (left c)).toData.toBits)∈FP:=
    mem_FP_of_eq (Term.variableBits_mem_FP hl) (fun _=>Term.variableBits_eq _)
  have HR:(fun c=>(Term.var (right c)).toData.toBits)∈FP:=
    mem_FP_of_eq (Term.variableBits_mem_FP hr) (fun _=>Term.variableBits_eq _)
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 HL
    (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (Term.const (-1)).toData.toBits) HR))
  intro c
  simp only [difference,Term.add_toBits,Term.mul_toBits]

theorem centerDifference_FP :
    (fun q=>(centerDifference (pairFst q) (pairSnd q).length).toData.toBits)∈FP:=
  difference_FP ((FormulaSignSlotMargin.initialDimension_unary.comp pairFst_mem_FP).add
    (UnaryFn.length pairSnd_mem_FP)) ((spatial_unary.comp pairFst_mem_FP).add (UnaryFn.length pairSnd_mem_FP))

theorem centerSquares_FP :(fun c=>(centerSquares c).toData.toBits)∈FP:=by
  have HF:=flatMap_range_mem_FP centerDifference_FP FormulaSignSlotSource.dimension_unary.mem_FP
  have HB:(fun c=>SumSquares.listBits (centerTerms c))∈FP:=by
    apply mem_FP_of_eq (mem_FP_comp HF Brackets.wrap_mem_FP)
    intro c
    simp only [Function.comp_apply,centerTerms,SumSquares.listBits,Data.toBits_l,List.map_map,
      List.flatten_eq_flatMap,List.flatMap_map,Function.comp_def,id_eq,Brackets.wrap,pairFst_pair,pairSnd_pair,
      List.length_replicate]
  apply mem_FP_of_eq (mem_FP_comp HB SumSquares.collapse_mem_FP)
  intro c
  rw [Function.comp_apply,SumSquares.collapse_listBits]
  rfl

theorem radiusDifference_FP :(fun c=>(radiusDifference c).toData.toBits)∈FP:=
  difference_FP (FormulaSignSlotMargin.initialDimension_unary.add FormulaSignSlotSource.dimension_unary)
    (spatial_unary.add FormulaSignSlotSource.dimension_unary)

theorem equation_FP :(fun c=>(equation c).toData.toBits)∈FP:=by
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 2
    (Codec.taggedTwo_mem_FP 2 FormulaSignSlotCenteredRadialSource.equation_FP centerSquares_FP)
    (Codec.taggedTwo_mem_FP 3 radiusDifference_FP radiusDifference_FP))
  intro c
  simp only [equation,Term.add_toBits,Term.square,Term.mul_toBits]

theorem equation_size_unary :UnaryFn (fun c=>(equation c).toData.size):=
  (UnaryFn.length equation_FP).of_eq (fun c=>Data.length_toBits (equation c).toData)

theorem scope (c :List Bool):(equation c).arity≤dimension c:=by
  have HB:(FormulaSignSlotCenteredRadialSource.equation c).arity≤dimension c:=
    (FormulaSignSlotCenteredRadialSource.scope c).trans (Nat.le_add_right (spatial c) (d c+1))
  have HC:(centerSquares c).arity≤dimension c:=by
    apply SumSquares.arity_accumulate_le _ _ _ (Nat.zero_le _)
    simp only [centerTerms,List.forall_mem_map,List.mem_range,centerDifference,difference,Term.arity]
    intro i hi
    dsimp only [dimension,spatial]
    omega
  have HR:(radiusDifference c).arity≤dimension c:=by
    simp only [radiusDifference,difference,Term.arity]
    dsimp only [dimension,spatial]
    omega
  simpa only [equation,Term.arity,Term.square,max_self] using max_le (max_le HB HC) HR

end LeanCanny.Encoding.FormulaSignSlotRadialFormalInput
