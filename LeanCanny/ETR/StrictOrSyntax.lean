/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.EquationSize
/-! # Exact syntax, truth and scopes for strict disjunctions -/
@[expose] public section
namespace LeanCanny.ETR.StrictOrSyntax

inductive Strict : Formula → Prop where
  | falsum : Strict .falsum
  | ltZero (t : Term) : Strict (.ltZero t)
  | or {p q} : Strict p → Strict q → Strict (.or p q)

def atoms : Formula → List Term
  | .ltZero t => [.mul (.const (-1)) t]
  | .or p q => atoms p++atoms q
  | _ => []

def nodes : Formula → ℕ
  | .or p q => 1+nodes p+nodes q
  | _ => 1

theorem nodes_pos (p : Formula) : 0<nodes p := by cases p <;> simp only [nodes] <;> omega

theorem nodes_le_size (p : Formula) : nodes p≤p.toData.size := by
  induction p with
  | or p q HP HQ =>
    simp only [nodes,Formula.toData,Data.cons_size,Data.size_empty,Codec.unary_size]
    omega
  | _ => exact Data.size_pos

theorem holds_iff {p : Formula} (hp : Strict p) (env : ℕ → ℝ) :
    p.Holds env ↔ ∃ t∈atoms p, 0<t.eval env := by
  induction hp with
  | falsum => simp [Formula.Holds,atoms]
  | ltZero t => simp only [Formula.Holds,atoms,List.mem_singleton,exists_eq_left,Term.eval,
      Int.cast_neg,Int.cast_one,neg_one_mul,neg_pos]
  | or _ _ HP HQ =>
    simp only [Formula.Holds,HP,HQ,atoms,List.mem_append,or_and_right,exists_or]

theorem atoms_scope {p : Formula} (hp : Strict p) (n : ℕ) (hs : p.arity≤n) :
    ∀ t∈atoms p, t.arity≤n := by
  induction hp with
  | falsum => simp only [atoms,List.not_mem_nil,false_implies,implies_true]
  | ltZero t =>
    intro u hu
    have HU : u=.mul (.const (-1)) t := List.mem_singleton.mp hu
    rw [HU]
    simpa only [Term.arity,Formula.arity,Nat.zero_max] using hs
  | or _ _ HP HQ =>
    intro t ht
    rcases List.mem_append.mp ht with H | H
    · exact HP (le_trans (Nat.le_max_left _ _) hs) t H
    · exact HQ (le_trans (Nat.le_max_right _ _) hs) t H

def forest (ps : List Formula) : List Bool := (ps.map Formula.encode).flatten
def measure (ps : List Formula) : ℕ := (ps.map nodes).sum

@[simp] theorem forest_nil : forest []=[] := rfl
@[simp] theorem forest_cons (p : Formula) (ps : List Formula) : forest (p::ps)=p.encode++forest ps := rfl
@[simp] theorem measure_nil : measure []=0 := rfl
@[simp] theorem measure_cons (p : Formula) (ps : List Formula) : measure (p::ps)=nodes p+measure ps := rfl

theorem measure_le_length (ps : List Formula) : measure ps≤(forest ps).length := by
  induction ps with
  | nil => exact le_rfl
  | cons p ps IH =>
    simp only [measure_cons,forest_cons,List.length_append,Formula.encode,Data.length_toBits]
    exact Nat.add_le_add (nodes_le_size p) IH

end LeanCanny.ETR.StrictOrSyntax
