/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.PositivePartWriter
public import LeanCanny.Encoding.MonotoneGateSource
public import LeanCanny.Encoding.FormulaConjunctionWriter
public import LeanCanny.Connectivity.ClosedFormulaWitness
/-! # Native closed positive-margin gates and one reciprocal root equation -/
@[expose] public section
namespace LeanCanny.Encoding.PositiveMarginSource
open LeanCanny.Computation ETR LeanCanny.Geometry LeanCanny.Connectivity
open MonotoneGateSource WeakCircleCanonicalFormula
open scoped Classical

def valueIndex (F : Family) (q : List Bool) : ℕ := dimension F q+index q

def operand (F : Family) (side : Bool) (q : List Bool) : Term :=
  let j:=if side then F.right q else F.left q
  if j < index q then .var (dimension F q+j) else .const 0

def body (F : Family) (q : List Bool) : Term :=
  if F.kind q=1 then .const 1 else
  if F.kind q=4 then .mul (operand F false q) (operand F true q) else
  if F.kind q=5 then .add (operand F false q) (operand F true q) else .const 0

def condition (F : Family) (q : List Bool) : Formula :=
  if F.kind q=2 then PositivePartGraph.condition (F.atom q) (valueIndex F q) else
    .eqZero (difference (.var (valueIndex F q)) (body F q))

def root (F : Family) (c : List Bool) : Term :=
  if F.count c=0 then .const 0 else .var (F.dimension c+(F.count c-1))
def reciprocal (F : Family) (c : List Bool) : Term :=
  difference (.mul (.var (F.dimension c+F.count c)) (root F c)) (.const 1)

def source (F : Family) (c : List Bool) : Formula :=
  .and (.eqZero (reciprocal F c)) (FormulaConjunctionWriter.rangeConjunction (condition F) F.count c)

def total (F : Family) (c : List Bool) : ℕ := F.dimension c+F.count c+1

private theorem variable_FP {n : List Bool → ℕ} (hn : UnaryFn n) :
    (fun q => (Term.var (n q)).toData.toBits) ∈ FP :=
  mem_FP_of_eq (Term.variableBits_mem_FP hn) (fun q => Term.variableBits_eq (n q))
private theorem add_FP {a b : List Bool → Term} (ha : (fun q => (a q).toData.toBits) ∈ FP)
    (hb : (fun q => (b q).toData.toBits) ∈ FP) : (fun q => (Term.add (a q) (b q)).toData.toBits) ∈ FP :=
  mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 ha hb) (fun q => (Term.add_toBits (a q) (b q)).symm)
private theorem mul_FP {a b : List Bool → Term} (ha : (fun q => (a q).toData.toBits) ∈ FP)
    (hb : (fun q => (b q).toData.toBits) ∈ FP) : (fun q => (Term.mul (a q) (b q)).toData.toBits) ∈ FP :=
  mem_FP_of_eq (Codec.taggedTwo_mem_FP 3 ha hb) (fun q => (Term.mul_toBits (a q) (b q)).symm)
private theorem difference_FP {a b : List Bool → Term} (ha : (fun q => (a q).toData.toBits) ∈ FP)
    (hb : (fun q => (b q).toData.toBits) ∈ FP) : (fun q => (difference (a q) (b q)).toData.toBits) ∈ FP :=
  add_FP ha (mul_FP (constFn_mem_FP _) hb)
private theorem iteTerm_FP {P : List Bool → Prop} [DecidablePred P] (hP : FPPred P)
    {a b : List Bool → Term} (ha : (fun q => (a q).toData.toBits) ∈ FP) (hb : (fun q => (b q).toData.toBits) ∈ FP) :
    (fun q => ((if P q then a q else b q)).toData.toBits) ∈ FP := by
  apply mem_FP_of_eq (hP.ite_mem_FP ha hb)
  intro q
  by_cases H : P q <;> simp only [H,ite_true,ite_false]

theorem valueIndex_unary (F : Family) (hF : Access F) : UnaryFn (valueIndex F) := (dimension_unary F hF).add index_unary

theorem operand_FP (F : Family) (hF : Access F) (side : Bool) : (fun q => (operand F side q).toData.toBits) ∈ FP := by
  have HI : UnaryFn (fun q => if side then F.right q else F.left q) := by cases side; exact hF.left; exact hF.right
  exact iteTerm_FP (FPPred.lt HI index_unary) (variable_FP ((dimension_unary F hF).add HI)) (constFn_mem_FP _)

theorem body_FP (F : Family) (hF : Access F) : (fun q => (body F q).toData.toBits) ∈ FP :=
  iteTerm_FP (BinaryFn.eq hF.kind (BinaryFn.const 1)) (constFn_mem_FP _)
    (iteTerm_FP (BinaryFn.eq hF.kind (BinaryFn.const 4)) (mul_FP (operand_FP F hF false) (operand_FP F hF true))
      (iteTerm_FP (BinaryFn.eq hF.kind (BinaryFn.const 5)) (add_FP (operand_FP F hF false) (operand_FP F hF true)) (constFn_mem_FP _)))

theorem condition_FP (F : Family) (hF : Access F) : (fun q => (condition F q).encode) ∈ FP := by
  have HP := PositivePartWriter.condition_FP hF.atom (valueIndex_unary F hF)
  have HE := Codec.taggedOne_mem_FP 1 (difference_FP (variable_FP (valueIndex_unary F hF)) (body_FP F hF))
  apply mem_FP_of_eq ((BinaryFn.eq hF.kind (BinaryFn.const 2)).ite_mem_FP HP HE)
  intro q
  by_cases H : F.kind q=2
  · simp only [condition,ite_eq_left H]
  · simp only [condition,ite_eq_right H]
    exact Codec.taggedOne_toBits 1 _

theorem root_FP (F : Family) (hF : Access F) : (fun c => (root F c).toData.toBits) ∈ FP :=
  iteTerm_FP (FPPred.eq hF.count (UnaryFn.const 0)) (constFn_mem_FP _)
    (variable_FP (hF.dimension.add (hF.count.sub (UnaryFn.const 1))))

theorem reciprocal_FP (F : Family) (hF : Access F) : (fun c => (reciprocal F c).toData.toBits) ∈ FP :=
  difference_FP (mul_FP (variable_FP (hF.dimension.add hF.count)) (root_FP F hF)) (constFn_mem_FP _)

theorem source_FP (F : Family) (hF : Access F) : (fun c => (source F c).encode) ∈ FP := by
  have H := Codec.taggedTwo_mem_FP 4 (Codec.taggedOne_mem_FP 1 (reciprocal_FP F hF))
    (FormulaConjunctionWriter.range_FP (condition_FP F hF) hF.count)
  apply mem_FP_of_eq H
  intro c
  simp only [source,Formula.encode,Formula.toData,Codec.taggedTwo_toBits,Codec.taggedOne_toBits]

theorem condition_closed (F : Family) (q : List Bool) : ClosedFormulaWitness.Closed (condition F q) := by
  unfold condition
  split_ifs
  · exact .and (.nonnegative _) (.and (.nonnegative _) (.eqZero _))
  · exact .eqZero _

theorem source_closed (F : Family) (c : List Bool) : ClosedFormulaWitness.Closed (source F c) := by
  apply ClosedFormulaWitness.Closed.and (.eqZero _)
  have HC (ps : List Formula) (hp : ∀ p∈ps,ClosedFormulaWitness.Closed p) :
      ClosedFormulaWitness.Closed (FormulaConjunctionWriter.conjunction ps) := by
    induction ps with
    | nil => exact .verum
    | cons p ps IH => exact .and (hp p List.mem_cons_self) (IH (fun q hq => hp q (List.mem_cons_of_mem p hq)))
  apply HC
  simp only [List.forall_mem_map,List.mem_range]
  exact fun i _ => condition_closed F _

end LeanCanny.Encoding.PositiveMarginSource
