/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.PositiveMarginEndpoint
public import LeanCanny.Connectivity.PositiveMarginSourceSplitting
/-! # Exact endpoint semantics retain zero-margin old candidates -/
@[expose] public section
namespace LeanCanny.Connectivity.PositiveMarginGraph
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open MonotoneGateSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def reciprocalValue (r : ℝ) : ℝ := if r=0 then 0 else r⁻¹

theorem reciprocal_rule (r a : ℝ) : ((r=0 ∧ a=0) ∨ a*r=1) ↔ a=reciprocalValue r := by
  by_cases H : r=0
  · simp only [H,reciprocalValue,ite_true,true_and,mul_zero,zero_ne_one,or_false]
  · simp only [H,false_and,false_or,reciprocalValue,ite_false]
    simpa only [one_div] using (show a*r=1 ↔ a=1/r from (eq_div_iff H).symm)

theorem append_last_eval (N : ℕ) (y : Fin N → ℝ) (r : ℝ) :
    Formula.extend (Fin.append y (fun _ : Fin 1 => r)) N=r := by
  simp only [Formula.extend,dite_eq_left (show N<N+1 by omega)]
  change Fin.append y (fun _ : Fin 1 => r) (Fin.natAdd N (0 : Fin 1))=r
  exact Fin.append_right _ _ _

theorem conditions_arity_base (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (FormulaConjunctionWriter.rangeConjunction (PositiveMarginSource.condition F) F.count c).arity≤F.dimension c+F.count c := by
  apply FormulaConjunctionWriter.arity
  simp only [List.forall_mem_map,List.mem_range]
  intro i hi
  have H:=PositiveMarginSource.condition_arity F (pair c (List.replicate i true))
    (by simpa only [dimension,pairFst_pair] using ha i hi)
  simp only [PositiveMarginSource.valueIndex,dimension,index,pairFst_pair,pairSnd_pair,List.length_replicate] at H
  omega

theorem conditions_holds (F : Family) (c : List Bool) (y : Fin (F.dimension c+F.count c) → ℝ)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (FormulaConjunctionWriter.rangeConjunction (PositiveMarginSource.condition F) F.count c).Holds (Formula.extend y) ↔ y∈Sol F c := by
  simp only [FormulaConjunctionWriter.rangeConjunction,FormulaConjunctionWriter.holds,List.forall_mem_map,List.mem_range]
  exact conditions_iff F c y ha

theorem holds_projection (n m : ℕ) (y : Fin (n+m) → ℝ) (s : Formula) (hs : s.arity≤n) :
    s.Holds (Formula.extend y) ↔ s.Holds (Formula.extend (TriangularContinuousGraph.projection n m y)) := by
  apply Formula.holds_congr
  intro i hi
  have HI : i<n := hi.trans_le hs
  have HM : i<n+m := by omega
  simp only [Formula.extend,dite_eq_left HI,dite_eq_left HM,TriangularContinuousGraph.projection]
  rfl

theorem rule_append (F : Family) (c : List Bool) (y : Fin (F.dimension c+F.count c) → ℝ) (r : ℝ) :
    (PositiveMarginSource.endpointRule F c).Holds (Formula.extend (Fin.append y (fun _ : Fin 1 => r))) ↔
      r=reciprocalValue ((PositiveMarginSource.root F c).eval (Formula.extend y)) := by
  have HR:=eval_append _ y r _ (PositiveMarginSource.root_arity F c)
  simp only [PositiveMarginSource.endpointRule,Formula.Holds,PositiveMarginSource.reciprocal,
    WeakCircleCanonicalFormula.difference,Term.eval,Int.cast_neg,Int.cast_one,mul_one,← sub_eq_add_neg,sub_eq_zero]
  rw [append_last_eval,HR]
  exact reciprocal_rule _ _

theorem endpoint_append (F : Family) (c : List Bool) (s : Formula) (hs : s.arity≤F.dimension c)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (y : Fin (F.dimension c+F.count c) → ℝ) (r : ℝ) :
    (PositiveMarginSource.endpoint F s c).Holds (Formula.extend (Fin.append y (fun _ : Fin 1 => r))) ↔
      s.Holds (Formula.extend (TriangularContinuousGraph.projection (F.dimension c) (F.count c) y)) ∧
        y∈Sol F c ∧ r=reciprocalValue ((PositiveMarginSource.root F c).eval (Formula.extend y)) := by
  simp only [PositiveMarginSource.endpoint,Formula.Holds]
  rw [holds_append _ y r s (hs.trans (Nat.le_add_right _ _)),holds_projection _ _ y s hs,
    holds_append _ y r _ (conditions_arity_base F c ha),conditions_holds F c y ha,rule_append]

end LeanCanny.Connectivity.PositiveMarginGraph
