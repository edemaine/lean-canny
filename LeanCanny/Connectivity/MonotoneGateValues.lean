/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.MonotoneGateArithmetic
/-! # Exact arithmetic values of the source's unique previous-wire graph -/
@[expose] public section
namespace LeanCanny.Connectivity.MonotoneGateValues
open ETR Set LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open MonotoneGateSource MonotoneGateGraph MonotoneGateArithmetic
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def full (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ) :
    Fin (total F c) → ℝ := TriangularTermGraph.extend (base F c) (gate F c) x (F.count c)

noncomputable def value (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ)
    (i : Fin (F.count c)) : ℝ := full F c x ⟨base F c+i.val,by have H:=i.isLt; dsimp [total]; omega⟩

noncomputable def status (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ)
    (i : Fin (F.count c)) : Prop := (atomBody F (pair c (List.replicate i.val true))).eval (Formula.extend x)=0

theorem body_eval (F : MonotoneGateSource.Family) (q : List Bool) (env : ℕ → ℝ) :
    (body F q).eval env = realOperation (F.kind q) ((atomBody F q).eval env)
      ((child F false q).eval env) ((child F true q).eval env) := by
  unfold body realOperation
  split_ifs <;> simp only [Term.eval,Int.cast_zero,Int.cast_one,pow_two]

theorem atomBody_arity (F : MonotoneGateSource.Family) (q : List Bool) (hi : index q < count F q)
    (ha : (F.atom q).arity≤dimension F q) : (atomBody F q).arity≤dimension F q+2*count F q := by
  simp only [atomBody,Term.arity,witnessIndex,Bool.toNat_false,Bool.toNat_true]
  omega

theorem eval_prefix (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ)
    (t : Term) (ht : t.arity≤base F c) : t.eval (Formula.extend (full F c x)) = t.eval (Formula.extend x) := by
  apply Term.eval_congr
  intro j hj
  have HJ : j < base F c := hj.trans_le ht
  have HJT : j < total F c := by dsimp [total]; omega
  simp only [Formula.extend,dite_eq_left HJ,dite_eq_left HJT]
  exact TriangularTermGraph.old (base F c) (gate F c) x (F.count c) ⟨j,HJ⟩

theorem gate_value (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) (i : Fin (F.count c)) :
    value F c x i = (body F (pair c (List.replicate i.val true))).eval (Formula.extend (full F c x)) :=
  TriangularTermGraph.equations (base F c) (gate F c) (F.count c) (gate_scope F c ha) x i

noncomputable def childValue (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ)
    (i : Fin (F.count c)) (j : ℕ) : ℝ := if h : j < i.val then value F c x ⟨j,h.trans i.isLt⟩ else 1

private theorem variable_eval (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ)
    (j : ℕ) (hj : j < F.count c) :
    (Term.var (base F c+j)).eval (Formula.extend (full F c x)) = value F c x ⟨j,hj⟩ := by
  have HJ : base F c+j < total F c := by dsimp [total]; omega
  simp only [Term.eval,Formula.extend,dite_eq_left HJ]
  rfl

private theorem child_term_eval (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ)
    (i : Fin (F.count c)) (j : ℕ) :
    (if j < i.val then Term.var (base F c+j) else Term.const 1).eval (Formula.extend (full F c x)) =
      childValue F c x i j := by
  unfold childValue
  by_cases H : j < i.val
  · rw [ite_eq_left H,dite_eq_left H]
    exact variable_eval F c x j (H.trans i.isLt)
  · rw [ite_eq_right H,dite_eq_right H]
    simp only [Term.eval,Int.cast_one]

theorem child_eval (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ)
    (i : Fin (F.count c)) (side : Bool) :
    (child F side (pair c (List.replicate i.val true))).eval (Formula.extend (full F c x)) =
      childValue F c x i (if side then F.right (pair c (List.replicate i.val true)) else F.left (pair c (List.replicate i.val true))) := by
  let j := if side then F.right (pair c (List.replicate i.val true)) else F.left (pair c (List.replicate i.val true))
  unfold child
  simp only [index,pairSnd_pair,List.length_replicate]
  change (if j < i.val then Term.var (valueIndex F (pair c (List.replicate i.val true)) j) else Term.const 1).eval
    (Formula.extend (full F c x)) = childValue F c x i j
  have H : valueIndex F (pair c (List.replicate i.val true)) j = base F c+j := by
    simp only [valueIndex,dimension,count,pairFst_pair,base]
  rw [H]
  exact child_term_eval F c x i j

theorem root_value (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ)
    (hm : 0 < F.count c) : rootValue F c x = value F c x ⟨F.count c-1,by omega⟩ := by
  unfold rootValue root
  rw [ite_eq_right (Nat.ne_of_gt hm)]
  have HN : base F c+(F.count c-1) < total F c := by dsimp [total]; omega
  simp only [Term.eval]
  change (if h : base F c+(F.count c-1) < total F c then _ else 0)=_
  rw [dite_eq_left HN]
  rfl

end LeanCanny.Connectivity.MonotoneGateValues
