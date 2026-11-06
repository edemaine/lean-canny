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
Bit-level serialization is isolated in the `AbstractEncoding` helper.

The background complexity library is Complexitylib. Its PSPACE class means
that one deterministic Turing machine halts on every input and decides membership
using polynomially many work-tape cells in the input's bit length.
-/

@[expose] public section
noncomputable section
namespace LeanCanny.Abstract

/-- Integer polynomial expressions use constants, variables, addition, and
multiplication. In dimension `n`, variables are the indices `Fin n`. -/
inductive Term (n : ℕ) where
  | const : ℤ → Term n
  | var : Fin n → Term n
  | add : Term n → Term n → Term n
  | mul : Term n → Term n → Term n

/-- A Boolean formula compares polynomial expressions with zero, using equality
or strict inequality, and combines these assertions by negation, conjunction,
and disjunction. ETR existentially quantifies all occurring variables;
connectivity treats them as coordinates of the described space. -/
inductive Formula (n : ℕ) where
  | falsum : Formula n
  | eqZero : Term n → Formula n
  | ltZero : Term n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n

/-- Evaluate an integer polynomial expression at a real assignment `x`. -/
def Term.eval {n : ℕ} (x : Fin n → ℝ) : Term n → ℝ
  | .const z => z
  | .var i => x i
  | .add a b => a.eval x + b.eval x
  | .mul a b => a.eval x * b.eval x

/-- A formula describes a solution set in `ℝⁿ`, represented by `Fin n → ℝ`.
Negation, conjunction, and disjunction give complement, intersection, and union. -/
def Formula.solutionSet {n : ℕ} : Formula n → Set (Fin n → ℝ)
  | .falsum => ∅
  | .eqZero t => {x | t.eval x = 0}
  | .ltZero t => {x | t.eval x < 0}
  | .not p => p.solutionSetᶜ
  | .and p q => p.solutionSet ∩ q.solutionSet
  | .or p q => p.solutionSet ∪ q.solutionSet

/-- Connected formulas describe connected solution sets in `ℝⁿ`, allowing the
empty set (`IsPreconnected`). -/
def ConnectedFormulas (n : ℕ) : Set (Formula n) :=
  {p | IsPreconnected p.solutionSet}

/-- Reachable endpoint pairs describe two unique points joined by a continuous
path inside the solution set of `p` (`JoinedIn`). The endpoints may be irrational.
Each endpoint formula must have a singleton solution set. -/
def ReachableEndpoints {n : ℕ} (p : Formula n) : Set (Formula n × Formula n) :=
  {ab | ∃ x y, ab.1.solutionSet = {x} ∧ ab.2.solutionSet = {y} ∧
    JoinedIn p.solutionSet x y}

/-! ## Input convention

Inputs are explicit expression trees with binary integer coefficients and unary
variable indices and dimensions. `AbstractEncoding` implements the precise
serialization; the encoder applies it to the syntax above.
-/

/-- Serialize a formula using the stated input-size convention. -/
def Formula.encode {n : ℕ} : Formula n → List Bool :=
  AbstractEncoding.formula (@Term.rec n) (@Formula.rec n)

/-! ## Encoded decision problems

An encoding image contains exactly the encodings of the specified mathematical
inputs. Every other bitstring is rejected. Unions range over input dimensions
and, for point queries, the formula describing the space.
-/

/-- ETR consists of the encodings of real-satisfiable formulas. -/
def ETR : Set (List Bool) := ⋃ n, (@Formula.encode n) '' {p | p.solutionSet.Nonempty}

/-- Whole-space connectivity applies the input encoding to connected formulas. -/
def ConnectedLanguage : Set (List Bool) :=
  ⋃ n, AbstractEncoding.space Formula.encode n '' ConnectedFormulas n

/-- Point connectivity applies the input encoding to reachable endpoint pairs. -/
def PointLanguage : Set (List Bool) :=
  ⋃ n, ⋃ p : Formula n, AbstractEncoding.point Formula.encode n p '' ReachableEndpoints p

/-- The class ∃ℝ consists of binary languages reducible to ETR in polynomial time.
A reduction is a total algorithm on all input strings that preserves yes/no
answers; the background library's `PolyTimeReducible` includes its time bound. -/
def ExistsReal : Set (Set (List Bool)) :=
  {L | Cslib.Complexity.PolyTimeReducible Turing.MultiTapeTM.encBits
    Turing.MultiTapeTM.encBits L ETR}

/-- Theorem (Canny): existential real satisfiability is decidable in deterministic
polynomial space, including rejection of malformed binary inputs. -/
theorem etr_mem_PSPACE : ETR ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits :=
  AbstractBridge.finite_etr_upper_bound @Term.rec @Formula.rec (by constructor <;> intros <;> rfl)

/-- Corollary: every problem in ∃ℝ is decidable in deterministic polynomial space. -/
theorem existsReal_subset_PSPACE :
    ExistsReal ⊆ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits :=
  AbstractBridge.reduction_closure etr_mem_PSPACE

/-- Theorem: connectivity of an integer semialgebraic set is in PSPACE,
including singular and unbounded sets and accepting the empty set. -/
theorem connectedLanguage_mem_PSPACE :
    ConnectedLanguage ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits :=
  AbstractBridge.finite_connected_upper_bound @Term.rec @Formula.rec (by constructor <;> intros <;> rfl)

/-- Theorem: path connectivity between two formula-described points in an
integer semialgebraic set is in PSPACE, including endpoint validation. -/
theorem pointLanguage_mem_PSPACE :
    PointLanguage ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits :=
  AbstractBridge.finite_point_upper_bound @Term.rec @Formula.rec (by constructor <;> intros <;> rfl)

end LeanCanny.Abstract
