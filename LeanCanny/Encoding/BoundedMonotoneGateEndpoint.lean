/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.BoundedMonotoneGateBounds
public import LeanCanny.Encoding.MonotoneGateEndpoint
/-! # Native canonical endpoint formulas for bounded slack-circle coordinates -/
@[expose] public section
namespace LeanCanny.Encoding.BoundedMonotoneGateEndpoint
open ETR LeanCanny.Computation LeanCanny.Geometry MonotoneGateSource
open scoped Classical

def residual (F : Family) (q : List Bool) : Term :=
  .add (BoundedMonotoneGateSource.budget F (pairFst q)) (.mul (.const (-1))
    (.add (.mul (.var (witnessIndex F q false)) (.var (witnessIndex F q false)))
      (.mul (.var (witnessIndex F q true)) (.var (witnessIndex F q true)))))
def condition (F : Family) (q : List Bool) : Formula :=
  WeakCircleCanonicalFormula.formula (residual F q)
    (BoundedMonotoneGateSource.slackIndex F q false) (BoundedMonotoneGateSource.slackIndex F q true)
def endpoint (F : Family) (s : Formula) (c : List Bool) : Formula :=
  .and (MonotoneGateEndpoint.endpoint F s c)
    (FormulaConjunctionWriter.rangeConjunction (condition F) F.count c)

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

theorem residual_FP (F : Family) (hF : Access F) :
    (fun q => (residual F q).toData.toBits) ∈ FP := by
  have W (b : Bool) : (fun q => (Term.var (witnessIndex F q b)).toData.toBits) ∈ FP :=
    variable_FP (((dimension_unary F hF).add ((UnaryFn.const 2).mul index_unary)).add (UnaryFn.const b.toNat))
  exact add_FP (mem_FP_comp pairFst_mem_FP (BoundedMonotoneGateSource.budget_FP F hF))
    (mul_FP (constFn_mem_FP (Term.const (-1)).toData.toBits)
      (add_FP (mul_FP (W false) (W false)) (mul_FP (W true) (W true))))

theorem condition_FP (F : Family) (hF : Access F) :
    (fun q => (condition F q).encode) ∈ FP := by
  have H (b : Bool) : UnaryFn (fun q => BoundedMonotoneGateSource.slackIndex F q b) :=
    ((((dimension_unary F hF).add ((UnaryFn.const 3).mul (count_unary F hF))).add
      ((UnaryFn.const 2).mul index_unary)).add (UnaryFn.const b.toNat))
  exact WeakCircleCanonicalWriter.formula_FP (residual_FP F hF) (H false) (H true)

theorem endpoint_FP (F : Family) (hF : Access F) {s : List Bool → Formula}
    (hs : (fun c => (s c).encode) ∈ FP) :
    (fun c => (endpoint F (s c) c).encode) ∈ FP := by
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 4 (MonotoneGateEndpoint.endpoint_FP F hF hs)
    (FormulaConjunctionWriter.range_FP (condition_FP F hF) hF.count))
  intro c
  simp only [endpoint,Formula.encode,Formula.toData,Codec.taggedTwo_toBits]

theorem residual_arity (F : Family) (c : List Bool) (i : ℕ) (hi : i < F.count c)
    (ha : ∀ j < F.count c, (F.atom (BoundedMonotoneGateSource.query c j)).arity≤F.dimension c) :
    (residual F (BoundedMonotoneGateSource.query c i)).arity≤Connectivity.MonotoneGateGraph.total F c := by
  have H := BoundedMonotoneGateSource.budget_arity F c ha
  simp only [residual,Term.arity,witnessIndex,dimension,index,BoundedMonotoneGateSource.query,
    pairFst_pair,pairSnd_pair,List.length_replicate,Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
  dsimp [Connectivity.MonotoneGateGraph.total,Connectivity.MonotoneGateGraph.base]
  omega

theorem condition_arity (F : Family) (c : List Bool) (i : ℕ) (hi : i < F.count c)
    (ha : ∀ j < F.count c, (F.atom (BoundedMonotoneGateSource.query c j)).arity≤F.dimension c) :
    (condition F (BoundedMonotoneGateSource.query c i)).arity≤BoundedMonotoneGateSource.total F c := by
  have H := residual_arity F c i hi ha
  simp only [BoundedMonotoneGateSource.query] at H
  simp only [condition,WeakCircleCanonicalFormula.arity,BoundedMonotoneGateSource.slackIndex,
    dimension,count,index,BoundedMonotoneGateSource.query,pairFst_pair,pairSnd_pair,
    List.length_replicate,Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
  dsimp [BoundedMonotoneGateSource.total,Connectivity.MonotoneGateGraph.total,
    Connectivity.MonotoneGateGraph.base] at H ⊢
  omega

theorem endpoint_arity (F : Family) (s : Formula) (c : List Bool) (hs : s.arity≤F.dimension c)
    (ha : ∀ j < F.count c, (F.atom (BoundedMonotoneGateSource.query c j)).arity≤F.dimension c) :
    (endpoint F s c).arity≤BoundedMonotoneGateSource.total F c := by
  apply max_le ((MonotoneGateEndpoint.endpoint_arity F s c hs ha).trans (by
    dsimp [BoundedMonotoneGateSource.total,Connectivity.MonotoneGateGraph.total,
      Connectivity.MonotoneGateGraph.base]; omega))
  apply FormulaConjunctionWriter.arity
  simp only [List.forall_mem_map,List.mem_range]
  exact fun i hi => condition_arity F c i hi ha

end LeanCanny.Encoding.BoundedMonotoneGateEndpoint
