/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.PositiveMarginSourceSplitting
/-! # One literal coordinate for a polynomial objective, with a unique continuous graph -/
@[expose] public section
namespace LeanCanny.Geometry.TermCoordinateGraph
open ETR Set LeanCanny.Connectivity
open scoped Classical

def row (n : ℕ) (t : Term) : Term := .add (.var n) (.mul (.const (-1)) t)
def formula (n : ℕ) (p : Formula) (t : Term) : Formula := .and p (.eqZero (row n t))
def description (n : ℕ) (p : Formula) (t : Term) : Description := ⟨n+1,formula n p t⟩

theorem row_scope (n : ℕ) (t : Term) (ht : t.arity≤n) : (row n t).arity≤n+1 := by
  simp only [row,Term.arity]
  omega

theorem description_wellFormed (n : ℕ) (p : Formula) (t : Term) (hp : p.arity≤n) (ht : t.arity≤n) :
    (description n p t).WellFormed := max_le (hp.trans (Nat.le_succ n)) (row_scope n t ht)

theorem append_last (n : ℕ) (x : Fin n → ℝ) (r : ℝ) : Fin.append x (fun _ : Fin 1 => r) (Fin.last n)=r := by
  change Fin.append x (fun _ : Fin 1 => r) (Fin.natAdd n (0 : Fin 1))=r
  exact Fin.append_right _ _ _

theorem source_append (n : ℕ) (p : Formula) (t : Term) (hp : p.arity≤n) (ht : t.arity≤n)
    (x : Fin n → ℝ) (r : ℝ) :
    (formula n p t).Holds (Formula.extend (Fin.append x (fun _ : Fin 1 => r))) ↔
      p.Holds (Formula.extend x) ∧ r=t.eval (Formula.extend x) := by
  have HV : Formula.extend (Fin.append x (fun _ : Fin 1 => r)) n=r := by
    simp only [Formula.extend,dite_eq_left (Nat.lt_succ_self n)]
    exact append_last n x r
  simp only [formula,Formula.Holds,row,Term.eval,Int.cast_neg,Int.cast_one,neg_one_mul,
    ← sub_eq_add_neg,sub_eq_zero]
  rw [PositiveMarginGraph.holds_append n x r p hp,PositiveMarginGraph.eval_append n x r t ht,HV]

abbrev PairSpace (n : ℕ) (p : Formula) (t : Term) :=
  {z : (Fin n → ℝ) × ℝ // p.Holds (Formula.extend z.1) ∧ z.2=t.eval (Formula.extend z.1)}

noncomputable def pairHomeomorph (n : ℕ) (p : Formula) (t : Term) (hp : p.arity≤n) (ht : t.arity≤n) :
    PairSpace n p t ≃ₜ (description n p t).realization :=
  (PositiveMarginGraph.appendHomeomorph n).subtype (fun z => (source_append n p t hp ht z.1 z.2).symm)

noncomputable def pairBaseHomeomorph (n : ℕ) (p : Formula) (t : Term) :
    PairSpace n p t ≃ₜ (Description.mk n p).realization where
  toFun z := ⟨z.val.1,z.property.1⟩
  invFun x := ⟨(x.val,t.eval (Formula.extend x.val)),⟨x.property,rfl⟩⟩
  left_inv z := by
    apply Subtype.ext
    exact Prod.ext rfl z.property.2.symm
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.prodMk
    ((FormulaStrictWitness.continuous_eval n t).comp continuous_subtype_val)).subtype_mk _

noncomputable def homeomorph (n : ℕ) (p : Formula) (t : Term) (hp : p.arity≤n) (ht : t.arity≤n) :
    (description n p t).realization ≃ₜ (Description.mk n p).realization :=
  (pairHomeomorph n p t hp ht).symm.trans (pairBaseHomeomorph n p t)

theorem old_coordinate (n : ℕ) (p : Formula) (t : Term) (hp : p.arity≤n) (ht : t.arity≤n)
    (y : (description n p t).realization) (i : Fin n) :
    (homeomorph n p t hp ht y).val i=y.val (Fin.castAdd 1 i) := rfl

theorem objective_coordinate (n : ℕ) (p : Formula) (t : Term) (hp : p.arity≤n) (ht : t.arity≤n)
    (y : (description n p t).realization) :
    y.val (Fin.last n)=t.eval (Formula.extend (homeomorph n p t hp ht y).val) := by
  let v : Fin (n+1) → ℝ := y.val
  let E := PositiveMarginGraph.appendHomeomorph n
  have HY : (formula n p t).Holds (Formula.extend (Fin.append (E.symm v).1 (fun _ : Fin 1 => (E.symm v).2))) := by
    change (formula n p t).Holds (Formula.extend (E (E.symm v)))
    rw [E.apply_symm_apply]
    exact y.property
  have HH := ((source_append n p t hp ht _ _).mp HY).2
  have HE := congrArg (fun v : Fin (n+1) → ℝ => v (Fin.last n)) (E.apply_symm_apply v)
  change v (Fin.last n)=t.eval (Formula.extend (E.symm v).1)
  rw [← HE]
  exact (append_last n _ _).trans HH

end LeanCanny.Geometry.TermCoordinateGraph
