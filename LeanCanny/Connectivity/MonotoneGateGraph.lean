/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.MonotoneGateSourceBounds
public import LeanCanny.Geometry.TriangularTermGraph
/-! # The native gate equation has exactly its uniquely evaluated root fiber -/
@[expose] public section
namespace LeanCanny.Connectivity.MonotoneGateGraph
open Set ETR LeanCanny.Encoding LeanCanny.Geometry
open MonotoneGateSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def base (F : Family) (c : List Bool) : ℕ := F.dimension c+2*F.count c
def gate (F : Family) (c : List Bool) (i : ℕ) : Term := body F (pair c (List.replicate i true))
def total (F : Family) (c : List Bool) : ℕ := base F c+F.count c

def ZeroSet (F : Family) (c : List Bool) : Set (Fin (total F c) → ℝ) :=
  {y | (MonotoneGateSource.polynomial F c).eval (Formula.extend y)=0}

theorem gate_scope (F : Family) (c : List Bool)
    (ha : ∀ i<F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    ∀ i<F.count c, (gate F c i).arity≤base F c+i := by
  intro i hi
  have H := body_arity F (pair c (List.replicate i true))
    (by simpa only [index,count,pairFst_pair,pairSnd_pair,List.length_replicate] using hi)
    (by simpa only [dimension,pairFst_pair] using ha i hi)
  simpa only [gate,base,valueIndex,dimension,count,index,pairFst_pair,pairSnd_pair,List.length_replicate] using H

theorem constraint_zero_iff (F : Family) (c : List Bool) (i : Fin (F.count c)) (y : Fin (total F c) → ℝ) :
    (constraint F (pair c (List.replicate i.val true))).eval (Formula.extend y)=0 ↔
      y ⟨base F c+i.val,by have H:=i.isLt; dsimp [total]; omega⟩ = (gate F c i.val).eval (Formula.extend y) := by
  have HI : base F c+i.val < total F c := by have H:=i.isLt; dsimp [total]; omega
  simp only [constraint,Term.eval,valueIndex,dimension,count,index,pairFst_pair,pairSnd_pair,List.length_replicate,
    Int.cast_neg,Int.cast_one,neg_one_mul,← sub_eq_add_neg,sub_eq_zero]
  change (if h : base F c+i.val<total F c then y ⟨base F c+i.val,h⟩ else 0)=_ ↔ _
  rw [dite_eq_left HI]
  rfl

theorem zero_iff (F : Family) (c : List Bool) (y : Fin (total F c) → ℝ) :
    y∈ZeroSet F c ↔ (root F c).eval (Formula.extend y)=0 ∧
      y∈TriangularTermGraph.Solutions (base F c) (gate F c) (F.count c) := by
  rw [ZeroSet,mem_ofPred_eq,polynomial_zero_iff]
  apply and_congr_right
  intro _
  constructor
  · intro H i
    exact (constraint_zero_iff F c i y).mp (H i.val i.isLt)
  · intro H i hi
    exact (constraint_zero_iff F c ⟨i,hi⟩ y).mpr (H ⟨i,hi⟩)

noncomputable def rootValue (F : Family) (c : List Bool) (x : Fin (base F c) → ℝ) : ℝ :=
  (root F c).eval (Formula.extend (TriangularTermGraph.extend (base F c) (gate F c) x (F.count c)))

noncomputable def zeroHomeomorph (F : Family) (c : List Bool)
    (ha : ∀ i<F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    ZeroSet F c ≃ₜ {x : Fin (base F c) → ℝ // rootValue F c x=0} := by
  let R := {y : TriangularTermGraph.Solutions (base F c) (gate F c) (F.count c) //
    (root F c).eval (Formula.extend y.val)=0}
  let E : ZeroSet F c ≃ₜ R :=
    { toFun := fun y => ⟨⟨y.val,((zero_iff F c y.val).mp y.property).2⟩,((zero_iff F c y.val).mp y.property).1⟩
      invFun := fun y => ⟨y.val.val,(zero_iff F c y.val.val).mpr ⟨y.property,y.val.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let G := TriangularTermGraph.homeomorph (base F c) (gate F c) (F.count c) (gate_scope F c ha)
  exact E.trans (G.subtype (fun y => by
    change (root F c).eval (Formula.extend y.val)=0 ↔
      (root F c).eval (Formula.extend (TriangularTermGraph.extend (base F c) (gate F c)
        (TriangularTermGraph.projection (base F c) (F.count c) y.val) (F.count c)))=0
    rw [TriangularTermGraph.unique _ _ _ (gate_scope F c ha) y]))

end LeanCanny.Connectivity.MonotoneGateGraph
