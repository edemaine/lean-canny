/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.AbstractBridge

/-! # A formal abstract of Canny's real-algebraic PSPACE bounds

This file introduces integer polynomial expressions, existential real
satisfiability, semialgebraic connectivity, and their binary encodings. It proves
ETR ∈ PSPACE, ∃ℝ ⊆ PSPACE, and PSPACE bounds for point and whole-space
connectivity. To check that these are the intended results, a reader only needs
to inspect the definitions and theorem statements here. Lean checks the proofs
through `AbstractBridge` and the rest of the development.

The background complexity library is Complexitylib. Its PSPACE class means
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
and disjunction. ETR existentially quantifies all occurring variables;
connectivity treats them as coordinates of the described space. -/
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

/-- Arity is zero for closed expressions; otherwise it is one more than the
largest variable index. An input of dimension `n` requires arity at most `n`. -/
def Term.arity : Term → ℕ
  | .const _ => 0
  | .var i => i + 1
  | .add a b | .mul a b => max a.arity b.arity

def Formula.arity : Formula → ℕ
  | .falsum => 0
  | .eqZero t | .ltZero t => t.arity
  | .not p => p.arity
  | .and p q | .or p q => max p.arity q.arity

/-- Real satisfiability means that some assignment makes the formula true.
A finite formula uses only finitely many of the variables in `ℕ → ℝ`. -/
def Formula.Satisfiable (p : Formula) : Prop := ∃ x : ℕ → ℝ, p.Holds x

/-! ## Semialgebraic connectivity -/

/-- The solution set consists of the points in `ℝⁿ` satisfying the formula.
Here `Fin n → ℝ` represents `ℝⁿ`; evaluation extends these coordinates by zero. -/
def Formula.solutionSet (n : ℕ) (p : Formula) : Set (Fin n → ℝ) :=
  {x | p.Holds (fun i => if h : i < n then x ⟨i, h⟩ else 0)}

/-- Connected formulas describe connected solution sets in `ℝⁿ`, allowing the
empty set (`IsPreconnected`). Only variables below `n` may occur. -/
def ConnectedFormulas (n : ℕ) : Set Formula :=
  {p | p.arity ≤ n ∧ IsPreconnected (p.solutionSet n)}

/-- Reachable endpoint pairs describe two unique points joined by a continuous
path inside the solution set of `p` (`JoinedIn`). The endpoints may be irrational.
All three formulas must use only the `n` coordinates; each endpoint formula
must have a singleton solution set. -/
def ReachableEndpoints (n : ℕ) (p : Formula) : Set (Formula × Formula) :=
  {ab | p.arity ≤ n ∧ ab.1.arity ≤ n ∧ ab.2.arity ≤ n ∧
    ∃ x y, ab.1.solutionSet n = {x} ∧ ab.2.solutionSet n = {y} ∧
      JoinedIn (p.solutionSet n) x y}

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

/-- Encode a whole-space query by its tag, unary dimension, and formula. -/
def encodeSpace (n : ℕ) (p : Formula) : List Bool :=
  node [unary 1, unary n, p.encode]

/-- Encode a point query by its tag, unary dimension, space formula, and the two
endpoint formulas. -/
def encodePoint (n : ℕ) (p : Formula) (ab : Formula × Formula) : List Bool :=
  node [unary 0, unary n, p.encode, ab.1.encode, ab.2.encode]

/-! ## Encoded decision problems

An encoding image contains exactly the encodings of the specified mathematical
inputs. Every other bitstring is rejected. Unions range over input dimensions
and, for point queries, the formula describing the space.
-/

/-- ETR consists of the encodings of real-satisfiable formulas. -/
def ETR : Set (List Bool) := Formula.encode '' {p | p.Satisfiable}

/-- Whole-space connectivity applies the input encoding to connected formulas. -/
def ConnectedLanguage : Set (List Bool) :=
  ⋃ n, encodeSpace n '' ConnectedFormulas n

/-- Point connectivity applies the input encoding to reachable endpoint pairs. -/
def PointLanguage : Set (List Bool) :=
  ⋃ n, ⋃ p, encodePoint n p '' ReachableEndpoints n p

/-- The class ∃ℝ consists of binary languages reducible to ETR in polynomial time.
A reduction is a total algorithm on all input strings that preserves yes/no
answers; the background library's `PolyTimeReducible` includes its time bound. -/
def ExistsReal : Set (Set (List Bool)) :=
  {L | Cslib.Complexity.PolyTimeReducible Turing.MultiTapeTM.encBits
    Turing.MultiTapeTM.encBits L ETR}

/- A private proof adapter supplies the bridge's syntax and its defining laws.
The mathematical definitions and theorem statements above and below do not
refer to this adapter. -/
private def presentation : AbstractBridge.Presentation where
  Term := Term
  Formula := Formula
  const := Term.const
  var := Term.var
  add := Term.add
  mul := Term.mul
  falsum := Formula.falsum
  eqZero := Formula.eqZero
  ltZero := Formula.ltZero
  not := Formula.not
  and := Formula.and
  or := Formula.or
  term_induction := @Term.rec
  formula_induction := @Formula.rec
  eval := Term.eval
  holds := Formula.Holds
  termCode := Term.encode
  formulaCode := Formula.encode
  termArity := Term.arity
  formulaArity := Formula.arity

private theorem laws : AbstractBridge.Laws presentation := by constructor <;> intros <;> rfl

/-- Theorem (Canny): existential real satisfiability is decidable in deterministic
polynomial space, including rejection of malformed binary inputs. -/
theorem etr_mem_PSPACE : ETR ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits :=
  AbstractBridge.etr_image_upper_bound presentation laws

/-- Corollary: every problem in ∃ℝ is decidable in deterministic polynomial space. -/
theorem existsReal_subset_PSPACE :
    ExistsReal ⊆ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits :=
  AbstractBridge.reduction_closure etr_mem_PSPACE

/-- Theorem: connectivity of an integer semialgebraic set is in PSPACE,
including singular and unbounded sets and accepting the empty set. -/
theorem connectedLanguage_mem_PSPACE :
    ConnectedLanguage ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits :=
  AbstractBridge.connected_image_upper_bound presentation laws

/-- Theorem: path connectivity between two formula-described points in an
integer semialgebraic set is in PSPACE, including endpoint validation. -/
theorem pointLanguage_mem_PSPACE :
    PointLanguage ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits :=
  AbstractBridge.point_image_upper_bound presentation laws

end LeanCanny.Abstract
