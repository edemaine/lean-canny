/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.AbstractBridge

/-! # A formal abstract of Canny's ETR PSPACE upper bound

This file introduces integer polynomial expressions, existential real
satisfiability, and their binary encoding, and proves ETR ∈ PSPACE and
∃ℝ ⊆ PSPACE. To check that these are the intended results, a reader only needs
to inspect the definitions and theorem statements here. Lean checks the proofs
through `AbstractBridge` and the rest of the development.

The background complexity library is Complexitylib2. Its PSPACE class means
that one deterministic Turing machine halts on every input and decides membership
using polynomially many work-tape cells in the input's bit length.
-/

@[expose] public section
namespace LeanCanny.Abstract

/-- Integer polynomial expressions use constants, variables, addition, and
multiplication. Variable names are natural numbers. -/
inductive Term where
  | const : ℤ → Term
  | var : ℕ → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term

/-- A Boolean formula compares polynomial expressions with zero, using equality
or strict inequality, and combines these assertions by negation, conjunction,
and disjunction. All occurring variables will be existentially quantified. -/
inductive Formula where
  | falsum : Formula
  | eqZero : Term → Formula
  | ltZero : Term → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula

/-- Evaluate an integer polynomial expression at a real assignment `x`. -/
def Term.eval (x : ℕ → ℝ) : Term → ℝ
  | .const z => z
  | .var i => x i
  | .add a b => a.eval x + b.eval x
  | .mul a b => a.eval x * b.eval x

/-- Truth of a formula at a real assignment has the usual Boolean semantics. -/
def Formula.Holds (x : ℕ → ℝ) : Formula → Prop
  | .falsum => False
  | .eqZero t => t.eval x = 0
  | .ltZero t => t.eval x < 0
  | .not p => ¬ p.Holds x
  | .and p q => p.Holds x ∧ q.Holds x
  | .or p q => p.Holds x ∨ q.Holds x

/-- Real satisfiability means that some assignment makes the formula true.
A finite formula uses only finitely many of the variables in `ℕ → ℝ`. -/
def Formula.Satisfiable (p : Formula) : Prop := ∃ x : ℕ → ℝ, p.Holds x

/-! ## Binary input convention

The size of an input is its literal bit length. A node is encoded by an opening
`false`, its children in order, and a closing `true`. Constructor tags and variable
indices are unary; integer magnitudes are canonical little-endian binary.
Lists record the ordered children of a syntax node.
-/

def node (children : List (List Bool)) : List Bool := false :: (children.flatten ++ [true])
def unary (n : ℕ) : List Bool := node (List.replicate n (node []))
def bit (b : Bool) : List Bool := if b then node [node []] else node []

/-- Nonnegative integers carry sign tag zero. Negative integers `-(n+1)` carry
sign tag one and magnitude field `n`, giving a unique representation of zero. -/
def integer : ℤ → List Bool
  | .ofNat n => node [unary 0, node (n.bits.map bit)]
  | .negSucc n => node [unary 1, node (n.bits.map bit)]

/-- Expression tags, in order, are constant, variable, addition, multiplication. -/
def Term.encode : Term → List Bool
  | .const z => node [unary 0, integer z]
  | .var i => node [unary 1, unary i]
  | .add a b => node [unary 2, a.encode, b.encode]
  | .mul a b => node [unary 3, a.encode, b.encode]

/-- Formula tags, in order, are false, equality, strict inequality, negation,
conjunction, disjunction. The encoding includes the entire formula. -/
def Formula.encode : Formula → List Bool
  | .falsum => node [unary 0]
  | .eqZero t => node [unary 1, t.encode]
  | .ltZero t => node [unary 2, t.encode]
  | .not p => node [unary 3, p.encode]
  | .and p q => node [unary 4, p.encode, q.encode]
  | .or p q => node [unary 5, p.encode, q.encode]

/-- ETR is the language of encodings of satisfiable existential real formulas.
Every other bitstring is rejected. -/
def ETR : Set (List Bool) := {bits | ∃ p : Formula, bits = p.encode ∧ p.Satisfiable}

/-- The class ∃ℝ consists of binary languages reducible to ETR in polynomial time.
A reduction is a total algorithm on all input strings that preserves yes/no
answers; the background library's `PolyTimeReducible` includes its time bound. -/
def ExistsReal : Set (Set (List Bool)) :=
  {L | Cslib.Complexity.PolyTimeReducible Turing.MultiTapeTM.encBits
    Turing.MultiTapeTM.encBits L ETR}

/-- Theorem (Canny): existential real satisfiability is decidable in deterministic
polynomial space, including rejection of malformed binary inputs. -/
theorem etr_mem_PSPACE : ETR ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits := by
  exact AbstractBridge.upper_bound
    { Term := Term, Formula := Formula
      const := Term.const, var := Term.var, add := Term.add, mul := Term.mul
      falsum := Formula.falsum, eqZero := Formula.eqZero, ltZero := Formula.ltZero
      not := Formula.not, and := Formula.and, or := Formula.or
      term_induction := @Term.rec, formula_induction := @Formula.rec
      eval := Term.eval, holds := Formula.Holds
      termCode := Term.encode, formulaCode := Formula.encode }
    (by constructor <;> intros <;> rfl)

/-- Corollary: every problem in ∃ℝ is decidable in deterministic polynomial space. -/
theorem existsReal_subset_PSPACE :
    ExistsReal ⊆ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits := by
  exact AbstractBridge.reduction_closure etr_mem_PSPACE

end LeanCanny.Abstract
