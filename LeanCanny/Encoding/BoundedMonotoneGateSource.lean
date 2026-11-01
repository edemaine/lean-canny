/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.MonotoneGateSourceBounds
/-! # Native bounded slack-circle equations for the closed Boolean gate source

The old gate coordinates are retained literally. Two slack coordinates per
wire bound all circular witnesses by one sum of squares of original atoms.
-/
@[expose] public section
namespace LeanCanny.Encoding.BoundedMonotoneGateSource
open LeanCanny.Computation ETR MonotoneGateSource
open scoped Classical

def query (c : List Bool) (i : ℕ) := pair c (List.replicate i true)
def atoms (F : Family) (c : List Bool) : List Term :=
  (List.range (F.count c)).map (fun i => F.atom (query c i))
def budget (F : Family) (c : List Bool) : Term :=
  .add (.const 1) (SumSquares.accumulate (atoms F c) (.const 0))
def slackIndex (F : Family) (q : List Bool) (b : Bool) :=
  dimension F q+3*count F q+2*index q+b.toNat

def slack (F : Family) (q : List Bool) : Term :=
  let square (i : ℕ) := Term.mul (.var i) (.var i)
  .add (.add (.add (square (witnessIndex F q false)) (square (witnessIndex F q true)))
    (.add (square (slackIndex F q false)) (square (slackIndex F q true))))
    (.mul (.const (-1)) (budget F (pairFst q)))
def slacks (F : Family) (c : List Bool) : List Term :=
  (List.range (F.count c)).map (fun i => slack F (query c i))
def polynomial (F : Family) (c : List Bool) : Term :=
  .add (.mul (MonotoneGateSource.polynomial F c) (MonotoneGateSource.polynomial F c))
    (SumSquares.accumulate (slacks F c) (.const 0))
def total (F : Family) (c : List Bool) := F.dimension c+2*F.count c+F.count c+2*F.count c

private theorem variable_FP {n : List Bool → ℕ} (hn : UnaryFn n) :
    (fun q => (Term.var (n q)).toData.toBits) ∈ FP :=
  mem_FP_of_eq (Term.variableBits_mem_FP hn) (fun _ => Term.variableBits_eq _)
private theorem add_FP {a b : List Bool → Term}
    (ha : (fun q => (a q).toData.toBits) ∈ FP) (hb : (fun q => (b q).toData.toBits) ∈ FP) :
    (fun q => (Term.add (a q) (b q)).toData.toBits) ∈ FP :=
  mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 ha hb) (fun _ => (Term.add_toBits _ _).symm)
private theorem mul_FP {a b : List Bool → Term}
    (ha : (fun q => (a q).toData.toBits) ∈ FP) (hb : (fun q => (b q).toData.toBits) ∈ FP) :
    (fun q => (Term.mul (a q) (b q)).toData.toBits) ∈ FP :=
  mem_FP_of_eq (Codec.taggedTwo_mem_FP 3 ha hb) (fun _ => (Term.mul_toBits _ _).symm)

private theorem atomsBits_FP (F : Family) (hF : Access F) :
    (fun c => SumSquares.listBits (atoms F c)) ∈ FP := by
  have H := flatMap_range_mem_FP hF.atom hF.count.mem_FP
  have HR : (fun c => (List.range (F.count c)).flatMap (fun i =>
      (F.atom (query c i)).toData.toBits)) ∈ FP := by
    simpa only [query,List.length_replicate] using H
  apply mem_FP_of_eq (mem_FP_comp HR Brackets.wrap_mem_FP)
  intro c
  simp only [Function.comp_apply,atoms,SumSquares.listBits,Data.toBits_l,List.map_map,
    List.flatten_eq_flatMap,List.flatMap_map,Function.comp_def,id_eq,Brackets.wrap]

theorem budget_FP (F : Family) (hF : Access F) :
    (fun c => (budget F c).toData.toBits) ∈ FP := by
  have H : (fun c => (SumSquares.accumulate (atoms F c) (.const 0)).toData.toBits) ∈ FP := by
    apply mem_FP_of_eq (mem_FP_comp (atomsBits_FP F hF) SumSquares.collapse_mem_FP)
    intro c
    rw [Function.comp_apply,SumSquares.collapse_listBits]
  exact add_FP (constFn_mem_FP (Term.const 1).toData.toBits) H

theorem slack_FP (F : Family) (hF : Access F) :
    (fun q => (slack F q).toData.toBits) ∈ FP := by
  have W (b : Bool) : (fun q => (Term.var (witnessIndex F q b)).toData.toBits) ∈ FP :=
    variable_FP (((dimension_unary F hF).add ((UnaryFn.const 2).mul index_unary)).add (UnaryFn.const b.toNat))
  have U (b : Bool) : (fun q => (Term.var (slackIndex F q b)).toData.toBits) ∈ FP :=
    variable_FP ((((dimension_unary F hF).add ((UnaryFn.const 3).mul (count_unary F hF))).add
      ((UnaryFn.const 2).mul index_unary)).add (UnaryFn.const b.toNat))
  exact add_FP (add_FP (add_FP (mul_FP (W false) (W false)) (mul_FP (W true) (W true)))
    (add_FP (mul_FP (U false) (U false)) (mul_FP (U true) (U true))))
    (mul_FP (constFn_mem_FP (Term.const (-1)).toData.toBits) (mem_FP_comp pairFst_mem_FP (budget_FP F hF)))

private theorem slacksBits_FP (F : Family) (hF : Access F) :
    (fun c => SumSquares.listBits (slacks F c)) ∈ FP := by
  have H := flatMap_range_mem_FP (slack_FP F hF) hF.count.mem_FP
  have HR : (fun c => (List.range (F.count c)).flatMap (fun i =>
      (slack F (query c i)).toData.toBits)) ∈ FP := by
    simpa only [query,List.length_replicate] using H
  apply mem_FP_of_eq (mem_FP_comp HR Brackets.wrap_mem_FP)
  intro c
  simp only [Function.comp_apply,slacks,SumSquares.listBits,Data.toBits_l,List.map_map,
    List.flatten_eq_flatMap,List.flatMap_map,Function.comp_def,id_eq,Brackets.wrap]

theorem polynomial_FP (F : Family) (hF : Access F) :
    (fun c => (polynomial F c).toData.toBits) ∈ FP := by
  have H : (fun c => (SumSquares.accumulate (slacks F c) (.const 0)).toData.toBits) ∈ FP := by
    apply mem_FP_of_eq (mem_FP_comp (slacksBits_FP F hF) SumSquares.collapse_mem_FP)
    intro c
    rw [Function.comp_apply,SumSquares.collapse_listBits]
  exact add_FP (mul_FP (MonotoneGateSource.polynomial_FP F hF) (MonotoneGateSource.polynomial_FP F hF)) H

theorem total_unary (F : Family) (hF : Access F) : UnaryFn (total F) :=
  ((hF.dimension.add ((UnaryFn.const 2).mul hF.count)).add hF.count).add
    ((UnaryFn.const 2).mul hF.count)

theorem polynomial_zero (F : Family) (c : List Bool) (env : ℕ → ℝ) :
    (polynomial F c).eval env=0 ↔ (MonotoneGateSource.polynomial F c).eval env=0 ∧
      ∀ i < F.count c, (slack F (query c i)).eval env=0 := by
  have HN : 0≤(SumSquares.accumulate (slacks F c) (.const 0)).eval env := by
    rw [SumSquares.eval_accumulate]
    simp only [Term.eval,Int.cast_zero,zero_add]
    exact Term.eval_sumSquares_nonneg _ _
  have HE : (polynomial F c).eval env=0 ↔
      (MonotoneGateSource.polynomial F c).eval env=0 ∧
      (SumSquares.accumulate (slacks F c) (.const 0)).eval env=0 := by
    simp only [polynomial,Term.eval]
    constructor
    · intro H
      constructor <;> nlinarith [sq_nonneg ((MonotoneGateSource.polynomial F c).eval env)]
    · rintro ⟨H,H'⟩
      rw [H,H']
      norm_num
  rw [HE,SumSquares.accumulate_zero_iff]
  simp only [slacks,List.forall_mem_map,List.mem_range]

end LeanCanny.Encoding.BoundedMonotoneGateSource
