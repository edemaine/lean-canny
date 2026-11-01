/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.StrictUnionWitnessFormula
public import LeanCanny.Encoding.MonotoneGateSource
/-! # Native polynomial-time controls for attenuated strict-union source equations -/
@[expose] public section
namespace LeanCanny.Encoding.StrictUnionWitnessWriter
open LeanCanny.Computation ETR LeanCanny.Connectivity StrictUnionWitnessFormula MonotoneGateSource
open scoped Classical

private theorem variable_FP {n : List Bool → ℕ} (hn : UnaryFn n) :
    (fun q => (Term.var (n q)).toData.toBits) ∈ FP :=
  mem_FP_of_eq (Term.variableBits_mem_FP hn) (fun q => Term.variableBits_eq (n q))
private theorem add_FP {a b : List Bool → Term} (ha : (fun q => (a q).toData.toBits) ∈ FP)
    (hb : (fun q => (b q).toData.toBits) ∈ FP) : (fun q => (Term.add (a q) (b q)).toData.toBits) ∈ FP :=
  mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 ha hb) (fun q => (Term.add_toBits (a q) (b q)).symm)
private theorem mul_FP {a b : List Bool → Term} (ha : (fun q => (a q).toData.toBits) ∈ FP)
    (hb : (fun q => (b q).toData.toBits) ∈ FP) : (fun q => (Term.mul (a q) (b q)).toData.toBits) ∈ FP :=
  mem_FP_of_eq (Codec.taggedTwo_mem_FP 3 ha hb) (fun q => (Term.mul_toBits (a q) (b q)).symm)

def weightVariable (F : Family) (q : List Bool) : Term := .var (dimension F q+index q)
def circleVariable (F : Family) (q : List Bool) (b : Bool) : Term := .var (dimension F q+count F q+2*index q+b.toNat)
def equation (F : Family) (q : List Bool) : Term :=
  .add (.mul (F.atom q) (.add (.mul (circleVariable F q false) (circleVariable F q false))
    (.mul (circleVariable F q true) (circleVariable F q true))))
    (.mul (.const (-1)) (.mul (weightVariable F q) (weightVariable F q)))
def condition (F : Family) (q : List Bool) : Formula :=
  .and (.not (.ltZero (weightVariable F q))) (.eqZero (equation F q))

theorem weight_FP (F : Family) (hF : Access F) : (fun q => (weightVariable F q).toData.toBits) ∈ FP :=
  variable_FP ((dimension_unary F hF).add index_unary)

theorem circle_FP (F : Family) (hF : Access F) (b : Bool) : (fun q => (circleVariable F q b).toData.toBits) ∈ FP :=
  variable_FP (((dimension_unary F hF).add (count_unary F hF)).add ((UnaryFn.const 2).mul index_unary) |>.add (UnaryFn.const b.toNat))

theorem equation_FP (F : Family) (hF : Access F) : (fun q => (equation F q).toData.toBits) ∈ FP :=
  add_FP (mul_FP hF.atom (add_FP (mul_FP (circle_FP F hF false) (circle_FP F hF false))
    (mul_FP (circle_FP F hF true) (circle_FP F hF true))))
    (mul_FP (constFn_mem_FP _) (mul_FP (weight_FP F hF) (weight_FP F hF)))

theorem condition_FP (F : Family) (hF : Access F) : (fun q => (condition F q).encode) ∈ FP := by
  have H := Codec.taggedTwo_mem_FP 4 (Codec.taggedOne_mem_FP 3 (Codec.taggedOne_mem_FP 2 (weight_FP F hF)))
    (Codec.taggedOne_mem_FP 1 (equation_FP F hF))
  apply mem_FP_of_eq H
  intro q
  simp only [condition,Formula.encode,Formula.toData,Codec.taggedOne_toBits,Codec.taggedTwo_toBits]

theorem sumEquation_FP {n m : List Bool → ℕ} (hn : UnaryFn n) (hm : UnaryFn m) :
    (fun c => (sumEquation (n c) (m c)).toData.toBits) ∈ FP := by
  have HT := variable_FP ((hn.comp pairFst_mem_FP).add (UnaryFn.length pairSnd_mem_FP))
  have HF := flatMap_range_mem_FP HT hm.mem_FP
  have HP := mem_FP_comp (mem_FP_comp HF Brackets.wrap_mem_FP) TermSum.collapse_mem_FP
  have HS : (fun c => (TermSum.accumulate ((List.range (m c)).map (fun i => Term.var (n c+i))) (.const 0)).toData.toBits) ∈ FP := by
    apply mem_FP_of_eq HP
    intro c
    simp only [Function.comp_apply,List.length_replicate,pairFst_pair,pairSnd_pair]
    have HE : Brackets.wrap ((List.range (m c)).flatMap (fun i => (Term.var (n c+i)).toData.toBits))=
        SumSquares.listBits ((List.range (m c)).map (fun i => Term.var (n c+i))) := by
      simp only [SumSquares.listBits,Data.toBits_l,List.map_map,Function.comp_def,
        List.flatten_eq_flatMap,List.flatMap_map,id_eq]
      rfl
    rw [HE,TermSum.collapse_listBits]
  exact add_FP HS (constFn_mem_FP _)

def source (F : Family) (c : List Bool) : Formula :=
  .and (.eqZero (sumEquation (F.dimension c) (F.count c)))
    (FormulaConjunctionWriter.rangeConjunction (condition F) F.count c)

theorem source_FP (F : Family) (hF : Access F) : (fun c => (source F c).encode) ∈ FP := by
  have HS := Codec.taggedOne_mem_FP 1 (sumEquation_FP hF.dimension hF.count)
  have HC := FormulaConjunctionWriter.range_FP (condition_FP F hF) hF.count
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 4 HS HC)
  intro c
  simp only [source,Formula.encode,Formula.toData,Codec.taggedTwo_toBits,Codec.taggedOne_toBits]

end LeanCanny.Encoding.StrictUnionWitnessWriter
