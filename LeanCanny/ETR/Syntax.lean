/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Syntax and semantics of existential real arithmetic

Terms are integer polynomial expression trees. Atomic formulas compare a term with zero;
arbitrary Boolean combinations are allowed. A formula is an ETR instance: all its variables
are existentially quantified. `Formula.arity` bounds their indices, and
`Formula.satisfiable_iff_fin` makes the finite existential block explicit.

This syntax has no arbitrary real constants, division, or implicit function oracles.
-/

@[expose] public section

namespace LeanCanny.ETR

/-- Integer polynomial expressions with natural-number variable names. -/
inductive Term where
  | const : ℤ → Term
  | var : ℕ → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  deriving DecidableEq, Repr

namespace Term

/-- Evaluate a polynomial expression in a commutative ring. -/
def eval {R : Type*} [CommRing R] (env : ℕ → R) : Term → R
  | .const z => z
  | .var i => env i
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env

/-- The first variable index not used by the term, or zero for a closed term. -/
def arity : Term → ℕ
  | .const _ => 0
  | .var i => i + 1
  | .add a b | .mul a b => max a.arity b.arity

/-- Rename variables without changing constants or arithmetic operations. -/
def rename (f : ℕ → ℕ) : Term → Term
  | .const z => .const z
  | .var i => .var (f i)
  | .add a b => .add (a.rename f) (b.rename f)
  | .mul a b => .mul (a.rename f) (b.rename f)

@[simp] theorem eval_rename {R : Type*} [CommRing R] (env : ℕ → R)
    (f : ℕ → ℕ) (t : Term) : (t.rename f).eval env = t.eval (env ∘ f) := by
  induction t <;> simp_all [rename, eval, Function.comp_def]

/-- Evaluation depends only on the finitely many variable indices below `arity`. -/
theorem eval_congr {R : Type*} [CommRing R] (t : Term) (env env' : ℕ → R)
    (h : ∀ i < t.arity, env i = env' i) : t.eval env = t.eval env' := by
  induction t with
  | const z => rfl
  | var i => exact h i (Nat.lt_succ_self i)
  | add a b ha hb =>
      exact congrArg₂ (· + ·)
        (ha fun i hi => h i (hi.trans_le (Nat.le_max_left ..)))
        (hb fun i hi => h i (hi.trans_le (Nat.le_max_right ..)))
  | mul a b ha hb =>
      exact congrArg₂ (· * ·)
        (ha fun i hi => h i (hi.trans_le (Nat.le_max_left ..)))
        (hb fun i hi => h i (hi.trans_le (Nat.le_max_right ..)))

/-- The corresponding multivariate polynomial over the integers. -/
noncomputable def toPolynomial : Term → MvPolynomial ℕ ℤ
  | .const z => MvPolynomial.C z
  | .var i => MvPolynomial.X i
  | .add a b => a.toPolynomial + b.toPolynomial
  | .mul a b => a.toPolynomial * b.toPolynomial

@[simp] theorem eval₂_toPolynomial {R : Type*} [CommRing R] (env : ℕ → R) (t : Term) :
    MvPolynomial.eval₂ (Int.castRingHom R) env t.toPolynomial = t.eval env := by
  induction t with
  | const z => exact MvPolynomial.eval₂_C (Int.castRingHom R) env z
  | var i => exact MvPolynomial.eval₂_X (Int.castRingHom R) env i
  | add a b ha hb => simp [toPolynomial, eval, ha, hb]
  | mul a b ha hb => simp [toPolynomial, eval, ha, hb]

end Term

/-- Quantifier-free Boolean formulas over integer polynomial equalities and strict inequalities. -/
inductive Formula where
  | falsum : Formula
  | eqZero : Term → Formula
  | ltZero : Term → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  deriving DecidableEq, Repr

namespace Formula

/-- Truth under an assignment of real numbers to variables. -/
def Holds (env : ℕ → ℝ) : Formula → Prop
  | .falsum => False
  | .eqZero t => t.eval env = 0
  | .ltZero t => t.eval env < 0
  | .not p => ¬ p.Holds env
  | .and p q => p.Holds env ∧ q.Holds env
  | .or p q => p.Holds env ∨ q.Holds env

/-- The first variable index not used by the formula. -/
def arity : Formula → ℕ
  | .falsum => 0
  | .eqZero t | .ltZero t => t.arity
  | .not p => p.arity
  | .and p q | .or p q => max p.arity q.arity

/-- All variables of the finite formula are existentially quantified. -/
def Satisfiable (p : Formula) : Prop := ∃ env : ℕ → ℝ, p.Holds env

/-- Rename variables in every atomic polynomial. -/
def rename (f : ℕ → ℕ) : Formula → Formula
  | .falsum => .falsum
  | .eqZero t => .eqZero (t.rename f)
  | .ltZero t => .ltZero (t.rename f)
  | .not p => .not (p.rename f)
  | .and p q => .and (p.rename f) (q.rename f)
  | .or p q => .or (p.rename f) (q.rename f)

@[simp] theorem holds_rename (env : ℕ → ℝ) (f : ℕ → ℕ) (p : Formula) :
    (p.rename f).Holds env ↔ p.Holds (env ∘ f) := by
  induction p <;> simp_all [rename, Holds]

/-- Truth depends only on variables below the syntactic arity. -/
theorem holds_congr (p : Formula) (env env' : ℕ → ℝ)
    (h : ∀ i < p.arity, env i = env' i) : p.Holds env ↔ p.Holds env' := by
  induction p with
  | falsum => rfl
  | eqZero t => simp only [Holds, t.eval_congr env env' h]
  | ltZero t => simp only [Holds, t.eval_congr env env' h]
  | not p hp => exact not_congr (hp h)
  | and p q hp hq =>
      exact and_congr
        (hp fun i hi => h i (hi.trans_le (Nat.le_max_left ..)))
        (hq fun i hi => h i (hi.trans_le (Nat.le_max_right ..)))
  | or p q hp hq =>
      exact or_congr
        (hp fun i hi => h i (hi.trans_le (Nat.le_max_left ..)))
        (hq fun i hi => h i (hi.trans_le (Nat.le_max_right ..)))

/-- Extend a finite tuple by zero on all unused indices. -/
def extend {n : ℕ} (env : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then env ⟨i, h⟩ else 0

/-- The semantics uses an actual finite existential block of exactly `arity` variables. -/
theorem satisfiable_iff_fin (p : Formula) :
    p.Satisfiable ↔ ∃ env : Fin p.arity → ℝ, p.Holds (extend env) := by
  constructor
  · rintro ⟨env, h⟩
    refine ⟨fun i => env i.val, (p.holds_congr env _ ?_).mp h⟩
    intro i hi
    simp [extend, hi]
  · rintro ⟨env, h⟩
    exact ⟨extend env, h⟩

@[simp] theorem not_satisfiable_falsum : ¬ falsum.Satisfiable := by
  simp [Satisfiable, Holds]

@[simp] theorem satisfiable_eqZero_zero : (eqZero (.const 0)).Satisfiable := by
  exact ⟨fun _ => 0, by simp [Holds, Term.eval]⟩

end Formula
end LeanCanny.ETR
