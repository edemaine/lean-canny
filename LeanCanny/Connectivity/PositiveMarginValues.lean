/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.PositiveMarginGraph
/-! # Literal values of actual native positive-margin gates retain the original input -/
@[expose] public section
namespace LeanCanny.Connectivity.PositiveMarginValues
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open MonotoneGateSource PositiveMarginGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def full (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) : Fin (F.dimension c+F.count c) → ℝ :=
  TriangularContinuousGraph.extend (F.dimension c) (gate F c) x (F.count c)
noncomputable def value (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) (i : Fin (F.count c)) : ℝ :=
  full F c x ⟨F.dimension c+i.val,by have HI:=i.isLt; omega⟩
noncomputable def childValue (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ)
    (i : Fin (F.count c)) (j : ℕ) : ℝ := if h : j < i.val then value F c x ⟨j,h.trans i.isLt⟩ else 0

theorem value_gate (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) (i : Fin (F.count c)) :
    value F c x i=gate F c i.val (TriangularContinuousGraph.truncate (F.dimension c) (F.count c) i.val i.isLt.le (full F c x)) :=
  TriangularContinuousGraph.equations _ _ x _ i

theorem old_eval (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) (t : Term) (ht : t.arity≤F.dimension c) :
    t.eval (Formula.extend (full F c x))=t.eval (Formula.extend x) := by
  apply Term.eval_congr
  intro j hj
  have HJ : j<F.dimension c := hj.trans_le ht
  have HM : j<F.dimension c+F.count c := by omega
  simp only [Formula.extend,dite_eq_left HJ,dite_eq_left HM]
  exact TriangularContinuousGraph.old _ _ x _ ⟨j,HJ⟩

theorem atom_eval (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) (i : Fin (F.count c))
    (ha : (F.atom (pair c (List.replicate i.val true))).arity≤F.dimension c) :
    (F.atom (pair c (List.replicate i.val true))).eval (Formula.extend
      (TriangularContinuousGraph.truncate (F.dimension c) (F.count c) i.val i.isLt.le (full F c x)))=
      (F.atom (pair c (List.replicate i.val true))).eval (Formula.extend x) :=
  (eval_truncate _ _ _ i.isLt.le (full F c x) _ (ha.trans (Nat.le_add_right _ _))).symm.trans (old_eval F c x _ ha)

theorem operand_eval (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) (i : Fin (F.count c)) (side : Bool) :
    (PositiveMarginSource.operand F side (pair c (List.replicate i.val true))).eval (Formula.extend
      (TriangularContinuousGraph.truncate (F.dimension c) (F.count c) i.val i.isLt.le (full F c x)))=
      childValue F c x i (if side then F.right (pair c (List.replicate i.val true)) else F.left (pair c (List.replicate i.val true))) := by
  have HG (j : ℕ) :
      (if j < i.val then Term.var (F.dimension c+j) else .const 0).eval (Formula.extend
        (TriangularContinuousGraph.truncate (F.dimension c) (F.count c) i.val i.isLt.le (full F c x)))=
        childValue F c x i j := by
    unfold childValue
    by_cases H : j < i.val
    · rw [ite_eq_left H,dite_eq_left H]
      have HI : F.dimension c+j<F.dimension c+i.val := Nat.add_lt_add_left H _
      simp only [Term.eval,Formula.extend,dite_eq_left HI,TriangularContinuousGraph.truncate,value]
    · rw [ite_eq_right H,dite_eq_right H]
      simp only [Term.eval,Int.cast_zero]
  cases side
  · simpa only [PositiveMarginSource.operand,dimension,index,pairFst_pair,pairSnd_pair,List.length_replicate,
      Bool.coe_false,ite_false] using HG (F.left (pair c (List.replicate i.val true)))
  · simpa only [PositiveMarginSource.operand,dimension,index,pairFst_pair,pairSnd_pair,List.length_replicate,
      ite_true] using HG (F.right (pair c (List.replicate i.val true)))

theorem value_atom (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) (i : Fin (F.count c))
    (ha : (F.atom (pair c (List.replicate i.val true))).arity≤F.dimension c)
    (hk : F.kind (pair c (List.replicate i.val true))=2) :
    value F c x i=max ((F.atom (pair c (List.replicate i.val true))).eval (Formula.extend x)) 0 := by
  rw [value_gate]
  simp only [gate,ite_eq_left hk]
  rw [atom_eval F c x i ha]

theorem value_one (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) (i : Fin (F.count c))
    (hk : F.kind (pair c (List.replicate i.val true))=1) : value F c x i=1 := by
  rw [value_gate]
  simp only [gate,hk,show (1 : ℕ)≠2 by decide,ite_false,PositiveMarginSource.body,ite_true,Term.eval,Int.cast_one]

theorem value_zero (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) (i : Fin (F.count c))
    (hk : F.kind (pair c (List.replicate i.val true))=0) : value F c x i=0 := by
  rw [value_gate]
  simp only [gate,hk,show (0 : ℕ)≠2 by decide,show (0 : ℕ)≠1 by decide,show (0 : ℕ)≠4 by decide,
    show (0 : ℕ)≠5 by decide,ite_false,PositiveMarginSource.body,Term.eval,Int.cast_zero]

theorem value_mul (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) (i : Fin (F.count c))
    (hk : F.kind (pair c (List.replicate i.val true))=4) : value F c x i=
      childValue F c x i (F.left (pair c (List.replicate i.val true))) *
      childValue F c x i (F.right (pair c (List.replicate i.val true))) := by
  rw [value_gate]
  simp only [gate,hk,show (4 : ℕ)≠2 by decide,show (4 : ℕ)≠1 by decide,ite_false,
    PositiveMarginSource.body,ite_true,Term.eval]
  rw [operand_eval F c x i false,operand_eval F c x i true]
  rfl

theorem value_add (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) (i : Fin (F.count c))
    (hk : F.kind (pair c (List.replicate i.val true))=5) : value F c x i=
      childValue F c x i (F.left (pair c (List.replicate i.val true))) +
      childValue F c x i (F.right (pair c (List.replicate i.val true))) := by
  rw [value_gate]
  simp only [gate,hk,show (5 : ℕ)≠2 by decide,show (5 : ℕ)≠1 by decide,show (5 : ℕ)≠4 by decide,
    ite_false,PositiveMarginSource.body,ite_true,Term.eval]
  rw [operand_eval F c x i false,operand_eval F c x i true]
  rfl

end LeanCanny.Connectivity.PositiveMarginValues
