/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.PositiveMarginSourceBounds
public import LeanCanny.Geometry.TriangularContinuousGraph
/-! # The native closed margin conditions are their actual unique continuous gate graph -/
@[expose] public section
namespace LeanCanny.Connectivity.PositiveMarginGraph
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open MonotoneGateSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def gate (F : Family) (c : List Bool) (i : ℕ) (y : Fin (F.dimension c+i) → ℝ) : ℝ :=
  if F.kind (pair c (List.replicate i true))=2 then
    max ((F.atom (pair c (List.replicate i true))).eval (Formula.extend y)) 0
  else (PositiveMarginSource.body F (pair c (List.replicate i true))).eval (Formula.extend y)

theorem gate_continuous (F : Family) (c : List Bool) (i : ℕ) : Continuous (gate F c i) := by
  unfold gate
  split_ifs
  · exact (FormulaStrictWitness.continuous_eval _ _).max continuous_const
  · exact FormulaStrictWitness.continuous_eval _ _

theorem eval_truncate (n m i : ℕ) (hi : i≤m) (y : Fin (n+m) → ℝ) (t : Term) (ht : t.arity≤n+i) :
    t.eval (Formula.extend y)=t.eval (Formula.extend (TriangularContinuousGraph.truncate n m i hi y)) := by
  apply Term.eval_congr
  intro j hj
  have HI : j<n+i := hj.trans_le ht
  have HM : j<n+m := HI.trans_le (Nat.add_le_add_left hi n)
  simp only [Formula.extend,dite_eq_left HI,dite_eq_left HM,TriangularContinuousGraph.truncate]

theorem condition_iff (F : Family) (c : List Bool) (y : Fin (F.dimension c+F.count c) → ℝ)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (i : Fin (F.count c)) :
    (PositiveMarginSource.condition F (pair c (List.replicate i.val true))).Holds (Formula.extend y) ↔
      y ⟨F.dimension c+i.val,by have HI:=i.isLt; omega⟩=
        gate F c i.val (TriangularContinuousGraph.truncate (F.dimension c) (F.count c) i.val i.isLt.le y) := by
  have HI : F.dimension c+i.val<F.dimension c+F.count c := Nat.add_lt_add_left i.isLt _
  have HV : Formula.extend y (PositiveMarginSource.valueIndex F (pair c (List.replicate i.val true)))=
      y ⟨F.dimension c+i.val,HI⟩ := by
    simp only [PositiveMarginSource.valueIndex,dimension,index,pairFst_pair,pairSnd_pair,List.length_replicate,
      Formula.extend,dite_eq_left HI]
  have HA:=eval_truncate (F.dimension c) (F.count c) i.val i.isLt.le y _
    ((ha i.val i.isLt).trans (Nat.le_add_right _ _))
  have HB:=eval_truncate (F.dimension c) (F.count c) i.val i.isLt.le y _
    (by simpa only [PositiveMarginSource.valueIndex,dimension,index,pairFst_pair,pairSnd_pair,List.length_replicate] using
      PositiveMarginSource.body_arity F (pair c (List.replicate i.val true)))
  unfold PositiveMarginSource.condition gate
  by_cases HK : F.kind (pair c (List.replicate i.val true))=2
  · rw [ite_eq_left HK,ite_eq_left HK,PositivePartGraph.holds_iff,HV,HA]
  · rw [ite_eq_right HK,ite_eq_right HK]
    simp only [Formula.Holds,WeakCircleCanonicalFormula.difference,Term.eval,Int.cast_neg,Int.cast_one,
      neg_one_mul,← sub_eq_add_neg,sub_eq_zero]
    rw [HV,HB]

theorem conditions_iff (F : Family) (c : List Bool) (y : Fin (F.dimension c+F.count c) → ℝ)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (∀ i < F.count c, (PositiveMarginSource.condition F (pair c (List.replicate i true))).Holds (Formula.extend y)) ↔
      y∈TriangularContinuousGraph.Solutions (F.dimension c) (gate F c) (F.count c) := by
  constructor
  · intro H i
    exact (condition_iff F c y ha i).mp (H i.val i.isLt)
  · intro H i hi
    exact (condition_iff F c y ha ⟨i,hi⟩).mpr (H ⟨i,hi⟩)

end LeanCanny.Connectivity.PositiveMarginGraph
