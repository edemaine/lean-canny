/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import RealCountingHierarchy.AbstractBridge

/-! # A formal abstract of real sentences in the counting hierarchy

This file proves the counting-hierarchy upper bounds of OpenAI,
*Existential–universal real sentences in the counting hierarchy* (October 4, 2026):
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/etr-counting-hierarchy.pdf
These results are distinct from Canny's 1988 polynomial-space bounds.

It introduces integer polynomial expressions, Boolean formulas, their explicit
binary encoding, and existential and existential-universal real sentences.
It proves ETR ∈ C₂₆P, ∃ℝ ⊆ C₂₆P, and existential-universal truth ∈ C₆₀P.
The displayed grammar uses expression trees; the development also supplies
shared-circuit bridges through shallow gate equations.
To assess these claims, the reader need only inspect this file's definitions
and theorem statements. Lean verifies the proofs through `AbstractBridge`
and the established development.

CSLib Frontier supplies the background complexity classes: C₀P is polynomial
time, and Cⱼ₊₁P is strict-majority polynomial time with one fixed oracle from
CⱼP. A membership theorem supplies one uniform machine for every input length.
-/

@[expose] public section
namespace RealCountingHierarchy.Abstract

/-- Integer polynomial expressions use integer constants, natural-number variable
names, addition, and multiplication. Only finitely many variables occur in a term. -/
inductive Term where
  | const : ℤ → Term
  | var : ℕ → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term

/-- Boolean formulas compare polynomial expressions with zero and use negation,
conjunction, and disjunction. Strict positivity is expressible by negating a term. -/
inductive Formula where
  | falsum : Formula
  | eqZero : Term → Formula
  | ltZero : Term → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula

/-- An assignment gives a real value to each variable name. Polynomial expressions
have their usual interpretation in the real numbers. -/
def Term.eval (env : ℕ → ℝ) : Term → ℝ
  | .const z => z
  | .var i => env i
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env

/-- Truth of a Boolean polynomial formula under a real assignment. -/
def Formula.Holds (env : ℕ → ℝ) : Formula → Prop
  | .falsum => False
  | .eqZero t => t.eval env = 0
  | .ltZero t => t.eval env < 0
  | .not p => ¬ p.Holds env
  | .and p q => p.Holds env ∧ q.Holds env
  | .or p q => p.Holds env ∨ q.Holds env

/-- A formula is satisfiable when some real assignment makes it true. -/
def Formula.Satisfiable (p : Formula) : Prop := ∃ env : ℕ → ℝ, p.Holds env

/-- An existential-universal sentence chooses the values of variables `0,…,r-1`
and requires the formula to hold for every assignment to the remaining variables.
`Fin r → ℝ` is the chosen finite tuple; unused variable names have no effect.
The case `r = 0` has an empty existential block. -/
def SentenceHolds (r : ℕ) (p : Formula) : Prop :=
  ∃ x : Fin r → ℝ, ∀ env : ℕ → ℝ, (∀ i : Fin r, env i.val = x i) → p.Holds env

/-! ## Binary input convention

Balanced parentheses serialize syntax trees: `false` opens a node and `true`
closes it. Constructor tags and variable indices are unary. Integers use a sign
and a binary natural payload; `Int.negSucc n` means `-(n+1)`. The definitions below specify
the complete wire format, using only lists and ordinary natural-number bits.
-/

def node (children : List (List Bool)) : List Bool := false :: (children.flatten ++ [true])
def unaryBits (n : ℕ) : List Bool := node (List.replicate n (node []))
def naturalBits (n : ℕ) : List Bool :=
  node (n.bits.map fun b => if b then node [node []] else node [])
def integerBits : ℤ → List Bool
  | .ofNat n => node [unaryBits 0, naturalBits n]
  | .negSucc n => node [unaryBits 1, naturalBits n]

def Term.bits : Term → List Bool
  | .const z => node [unaryBits 0, integerBits z]
  | .var i => node [unaryBits 1, unaryBits i]
  | .add a b => node [unaryBits 2, a.bits, b.bits]
  | .mul a b => node [unaryBits 3, a.bits, b.bits]

def Formula.bits : Formula → List Bool
  | .falsum => node [unaryBits 0]
  | .eqZero t => node [unaryBits 1, t.bits]
  | .ltZero t => node [unaryBits 2, t.bits]
  | .not p => node [unaryBits 3, p.bits]
  | .and p q => node [unaryBits 4, p.bits, q.bits]
  | .or p q => node [unaryBits 5, p.bits, q.bits]

/-- ETR is the binary language of satisfiable formulas. Every word outside the
exact encoding image is rejected, so the decision problem has no input promise. -/
def ETR : Set (List Bool) := {w | ∃ p : Formula, w = p.bits ∧ p.Satisfiable}

/-- Two-block truth encodes a unary existential block length and a Boolean matrix,
using the background library's pair framing. Malformed inputs are rejected.
Every variable occurring outside the chosen prefix is universally quantified. -/
def ExistsForall : Set (List Bool) :=
  {w | ∃ r : ℕ, ∃ p : Formula,
    w = Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encBits
      (r, p.bits) ∧ SentenceHolds r p}

/-- The class ∃ℝ contains binary decision problems reducible to ETR in polynomial
time. A reduction is a total algorithm on all bitstrings preserving yes/no answers. -/
def ExistsReal : Set (Set (List Bool)) :=
  {L | Cslib.Complexity.PolyTimeReducible Turing.MultiTapeTM.encBits
    Turing.MultiTapeTM.encBits L ETR}

/-- Theorem (OpenAI, existential bound): ETR has one uniform C₂₆P decision procedure,
including rejection of malformed inputs. -/
theorem etr_mem_CountingLevel : ETR ∈ Cslib.Complexity.CountingLevel 26 Turing.MultiTapeTM.encBits := by
  exact AbstractBridge.etr_upper_bound
    (eval := Term.eval) (termCode := Term.bits)
    (node := node) (unary := unaryBits) (natural := naturalBits) (integer := integerBits)
    (termInduction := @Term.rec) (formulaInduction := @Formula.rec)

/-- Corollary: every decision problem in ∃ℝ belongs to the same fixed counting level. -/
theorem existsReal_subset_CountingLevel :
    ExistsReal ⊆ Cslib.Complexity.CountingLevel 26 Turing.MultiTapeTM.encBits := by
  intro L hL
  exact hL.mem_CountingLevel etr_mem_CountingLevel

/-- Theorem (OpenAI, two-block bound): existential-universal real truth is in the
counting hierarchy. This formalization supplies the fixed level C₆₀P, independent
of the input's variable counts, degrees, and coefficient magnitudes. -/
theorem existsForall_mem_CountingLevel :
    ExistsForall ∈ Cslib.Complexity.CountingLevel 60 Turing.MultiTapeTM.encBits := by
  exact AbstractBridge.existsForall_upper_bound
    (eval := Term.eval) (termCode := Term.bits)
    (node := node) (unary := unaryBits) (natural := naturalBits) (integer := integerBits)
    (termInduction := @Term.rec) (formulaInduction := @Formula.rec)

end RealCountingHierarchy.Abstract
