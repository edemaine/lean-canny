/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationSystem
public import LeanCanny.ETR.Grammar

/-!
# Negation normal form and its simultaneous positive/negative tree transform

Both polarities are computed together. Each Boolean child is used once in each
polarity, and arithmetic payloads are copied verbatim at atoms. The raw-data
extension has a linear size bound even on trees that are not formulas.
-/

@[expose] public section

namespace LeanCanny.ETR

namespace SignedFormula

def toFormula : SignedFormula → Formula
  | .truth => .not .falsum
  | .falsum => .falsum
  | .eqZero t => .eqZero t
  | .neZero t => .not (.eqZero t)
  | .ltZero t => .ltZero t
  | .nonneg t => .not (.ltZero t)
  | .and p q => .and p.toFormula q.toFormula
  | .or p q => .or p.toFormula q.toFormula

theorem holds_toFormula (p : SignedFormula) (env : ℕ → ℝ) :
    p.toFormula.Holds env ↔ p.Holds env := by
  induction p <;> simp_all [toFormula, Formula.Holds, Holds]

@[simp] theorem toFormula_arity (p : SignedFormula) : p.toFormula.arity = p.arity := by
  induction p <;> simp_all [toFormula, Formula.arity, arity]

@[simp] theorem toFormula_toSigned (p : SignedFormula) : p.toFormula.toSigned true = p := by
  induction p <;> simp_all [toFormula, Formula.toSigned]

end SignedFormula

namespace Formula

def IsNNF : Formula → Bool
  | .falsum | .eqZero _ | .ltZero _ => true
  | .not .falsum | .not (.eqZero _) | .not (.ltZero _) => true
  | .not _ => false
  | .and p q | .or p q => p.IsNNF && q.IsNNF

def nnf (p : Formula) (positive : Bool) : Formula := (p.toSigned positive).toFormula

@[simp] theorem nnf_arity (p : Formula) (positive : Bool) : (p.nnf positive).arity = p.arity := by
  rw [nnf, SignedFormula.toFormula_arity, toSigned_arity]

@[simp] theorem nnf_toSigned (p : Formula) (positive : Bool) :
    (p.nnf positive).toSigned true = p.toSigned positive := by
  rw [nnf, SignedFormula.toFormula_toSigned]

/-- The preprocessing phase leaves the existing equation compiler's output unchanged. -/
@[simp] theorem nnf_equationSystem (p : Formula) :
    (p.nnf true).equationSystem = p.equationSystem := by
  simp only [equationSystem, nnf_toSigned, nnf_arity]

theorem holds_nnf (p : Formula) (positive : Bool) (env : ℕ → ℝ) :
    (p.nnf positive).Holds env ↔ if positive then p.Holds env else ¬ p.Holds env :=
  ((p.toSigned positive).holds_toFormula env).trans (p.holds_toSigned positive env)

theorem nnf_isNNF (p : Formula) (positive : Bool) : (p.nnf positive).IsNNF = true := by
  have h : ∀ q : SignedFormula, q.toFormula.IsNNF = true := by
    intro q
    induction q <;> simp_all [SignedFormula.toFormula, IsNNF]
  exact h _

theorem satisfiable_nnf (p : Formula) : (p.nnf true).Satisfiable ↔ p.Satisfiable :=
  exists_congr (fun env => p.holds_nnf true env)

/-- Positive normalization fixes formulas that already have negations only at atoms. -/
theorem nnf_eq_self_of_isNNF (p : Formula) (hp : p.IsNNF = true) : p.nnf true = p := by
  induction p with
  | falsum => rfl
  | eqZero t => rfl
  | ltZero t => rfl
  | not p =>
      cases p <;> simp_all only [IsNNF, Bool.false_eq_true]
      all_goals rfl
  | and p q ihp ihq =>
      obtain ⟨hp, hq⟩ := Bool.and_eq_true_iff.mp hp
      change Formula.and (p.nnf true) (q.nnf true) = _
      rw [ihp hp, ihq hq]
  | or p q ihp ihq =>
      obtain ⟨hp, hq⟩ := Bool.and_eq_true_iff.mp hp
      change Formula.or (p.nnf true) (q.nnf true) = _
      rw [ihp hp, ihq hq]

end Formula

namespace NNF
open Complexity

def one (tag : ℕ) (d : Data) : Data := .l [Codec.unary tag, d]

def two (tag : ℕ) (d e : Data) : Data := .l [Codec.unary tag, d, e]

def falseData : Data := Formula.falsum.toData

def trueData : Data := one 3 falseData

def dual : Data → Data × Data
  | .l [tag, p] =>
      if tag = Codec.unary 1 ∨ tag = Codec.unary 2 then
        (.l [tag, p], one 3 (.l [tag, p]))
      else if tag = Codec.unary 3 then ((dual p).2, (dual p).1)
      else (falseData, trueData)
  | .l [tag, p, q] =>
      if tag = Codec.unary 4 then (two 4 (dual p).1 (dual q).1, two 5 (dual p).2 (dual q).2)
      else if tag = Codec.unary 5 then (two 5 (dual p).1 (dual q).1, two 4 (dual p).2 (dual q).2)
      else (falseData, trueData)
  | _ => (falseData, trueData)

theorem dual_formula (p : Formula) :
    dual p.toData = ((p.nnf true).toData, (p.nnf false).toData) := by
  induction p <;>
    simp_all [dual, Formula.toData, Formula.nnf, Formula.toSigned, SignedFormula.toFormula,
      falseData, trueData, one, two, Codec.unary]

@[simp] theorem one_size (tag : ℕ) (d : Data) : (one tag d).size = 2 * tag + d.size + 4 := by
  simp only [one, Data.cons_size, Codec.unary_size, Data.size_empty]
  omega

@[simp] theorem two_size (tag : ℕ) (d e : Data) :
    (two tag d e).size = 2 * tag + d.size + e.size + 4 := by
  simp only [two, Data.cons_size, Codec.unary_size, Data.size_empty]
  omega

@[simp] theorem falseData_size : falseData.size = 4 := by
  simp only [falseData, Formula.toData, Data.cons_size, Codec.unary_size, Data.size_empty]

@[simp] theorem trueData_size : trueData.size = 14 := by simp [trueData]

/-- Both candidate polarities together have linear size on every raw tree. -/
theorem dual_size (d : Data) : (dual d).1.size + (dual d).2.size ≤ 20 * d.size := by
  have key : ∀ (n : ℕ) (d : Data), d.size ≤ n →
      (dual d).1.size + (dual d).2.size ≤ 20 * d.size := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        rintro ⟨xs⟩ hn
        have hpos := @Data.size_pos (.l xs)
        rcases xs with _ | ⟨tag, _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩⟩
        · simp [dual]
        · simp only [dual, falseData_size, trueData_size]
          omega
        · have hp : p.size < n := (Data.size_lt_of_mem (by simp)).trans_le hn
          have hi := ih p.size hp p le_rfl
          simp only [dual]
          split
          · simp only [one_size]
            omega
          · split
            · simp only [Data.cons_size, Data.size_empty] at *
              omega
            · simp only [falseData_size, trueData_size]
              omega
        · have hp : p.size < n := (Data.size_lt_of_mem (by simp)).trans_le hn
          have hq : q.size < n := (Data.size_lt_of_mem (by simp)).trans_le hn
          have hi := ih p.size hp p le_rfl
          have hj := ih q.size hq q le_rfl
          have ht := @Data.size_pos tag
          simp only [dual]
          split
          · simp only [two_size, Data.cons_size, Data.size_empty] at *
            omega
          · split
            · simp only [two_size, Data.cons_size, Data.size_empty] at *
              omega
            · simp only [falseData_size, trueData_size]
              omega
        · simp only [dual, falseData_size, trueData_size]
          omega
  exact key d.size d le_rfl

end NNF
end LeanCanny.ETR
