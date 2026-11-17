/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Path

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy
public import CslibFrontier.Computability.Complexity.Classes.Space
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum

public import LeanCanny.AbstractBridge
public import LeanCanny.CountingHierarchy.AbstractBridge

/-! # A formal abstract of real-algebraic complexity bounds

This file introduces integer polynomial expressions, their real solution sets,
and a shared binary encoding. It proves ETR ∈ PSPACE, ∃ℝ ⊆ PSPACE, and PSPACE
bounds for semialgebraic connectivity following Canny (1988). It also proves
ETR ∈ C₂₆P, ∃ℝ ⊆ C₂₆P, and existential-universal real truth ∈ C₆₀P following
OpenAI, *Existential–universal real sentences in the counting hierarchy*
(October 4, 2026):
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/etr-counting-hierarchy.pdf

To assess these claims, the reader need only inspect the definitions and theorem
statements here. Lean verifies the proofs through the PSPACE and CH bridges and
the development. Both parts use exactly the same syntax, solution sets, and input
convention. The displayed grammar uses expression trees; the implementation also
supplies shared-circuit bridges through shallow gate equations.

CSLib Frontier supplies the background machine-based complexity classes. PSPACE
means one deterministic machine halts on every input using polynomially many
work-tape cells. C₀P is polynomial time, and Cⱼ₊₁P is strict-majority polynomial
time with one fixed oracle from CⱼP. The statements below include malformed input
rejection and one uniform machine for all input lengths.
-/

@[expose] public section
noncomputable section
namespace LeanCanny.Abstract

/-! ## Shared formulas and real solution sets -/

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

/-! ## Binary input convention

A flat prefix list records each constructor before its children, in field
order. Integer leaves use binary encoding; variable indices use unary encoding.
Other constructors receive consecutive unary tags, considering `Term` before
`Formula`; index tokens are shifted past those tags. The command below generates
local `Token`, `Term.tokens`, `Formula.tokens`, and `encoding` definitions.
CSLib Frontier frames each token once. Dimensions are unary; query framing has
fixed depth. Every language below contains exactly the encodings of its
specified mathematical inputs and rejects every other bitstring.
-/

derive_syntax_encoding Term Formula
  (integers := binary) (indices := unary)

/-! ## Existential real arithmetic -/

/-- ETR consists of the encodings of real-satisfiable formulas. -/
def ETR : Set (List Bool) := ⋃ n, (fun p : Formula n => encoding p.tokens) '' {p | p.solutionSet.Nonempty}

/-- The class ∃ℝ consists of binary languages reducible to ETR in polynomial time.
A reduction is a total algorithm on all input strings that preserves yes/no
answers; the background library's `PolyTimeReducible` includes its time bound. -/
def ExistsReal : Set (Set (List Bool)) :=
  {L | Cslib.Complexity.PolyTimeReducible Turing.MultiTapeTM.encBits
    Turing.MultiTapeTM.encBits L ETR}

/-- Theorem (Canny, 1988): existential real satisfiability is decidable in deterministic
polynomial space, including rejection of malformed binary inputs. -/
theorem etr_mem_PSPACE : ETR ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits :=
  AbstractBridge.etr_upper_bound

/-- Corollary (Canny, 1988): every problem in ∃ℝ is decidable in deterministic
polynomial space. -/
theorem existsReal_subset_PSPACE :
    ExistsReal ⊆ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits :=
  AbstractBridge.existsReal_upper_bound

/-- Theorem (OpenAI, 2026): ETR belongs to the fixed counting level C₂₆P,
with the same encoded language used in the PSPACE theorem above. -/
theorem etr_mem_CountingLevel :
    ETR ∈ Cslib.Complexity.CountingLevel 26 Turing.MultiTapeTM.encBits :=
  CountingHierarchy.AbstractBridge.etr_upper_bound

/-- Corollary (OpenAI, 2026): every problem in ∃ℝ belongs to that same fixed
counting level. -/
theorem existsReal_subset_CountingLevel :
    ExistsReal ⊆ Cslib.Complexity.CountingLevel 26 Turing.MultiTapeTM.encBits :=
  CountingHierarchy.AbstractBridge.existsReal_upper_bound etr_mem_CountingLevel

/-! ## Existential-universal real arithmetic -/

/-- An existential-universal sentence chooses a real tuple of length `r` and
requires the formula to hold for every real tuple of length `s`. `Fin.addCases`
concatenates the two tuples, with the existential coordinates first. Either
block may be empty. -/
def SentenceHolds {r s : ℕ} (p : Formula (r + s)) : Prop :=
  ∃ x : Fin r → ℝ, ∀ y : Fin s → ℝ, Fin.addCases x y ∈ p.solutionSet

/-- Existential-universal truth uses the same formula encoding as ETR and
records the unary existential block length. The union allows all finite block
sizes; unused coordinates do not affect truth. Every other word is rejected. -/
def ExistsForall : Set (List Bool) :=
  ⋃ r, ⋃ s, (fun p : Formula (r + s) =>
    Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary encoding (r, p.tokens)) ''
      {p | SentenceHolds p}

/-- Theorem (OpenAI, 2026): existential-universal real truth is in CH.
This formalization supplies the fixed level C₆₀P, independent of variable counts,
polynomial degrees, and coefficient magnitudes. -/
theorem existsForall_mem_CountingLevel :
    ExistsForall ∈ Cslib.Complexity.CountingLevel 60 Turing.MultiTapeTM.encBits :=
  CountingHierarchy.AbstractBridge.twoBlock_upper_bound

/-! ## Whole-space connectivity -/

/-- Connected formulas describe connected solution sets in `ℝⁿ`, allowing the
empty set (Mathlib's root-level `IsPreconnected`). -/
def ConnectedFormulas (n : ℕ) : Set (Formula n) :=
  {p | _root_.IsPreconnected p.solutionSet}

/-- Whole-space connectivity applies the input encoding to connected formulas. -/
def ConnectedLanguage : Set (List Bool) :=
  ⋃ n, (fun p : Formula n => Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary
    encoding (n, p.tokens)) '' ConnectedFormulas n

/-- Theorem (Canny, 1988): connectivity of an integer semialgebraic set is in PSPACE,
including singular and unbounded sets and accepting the empty set. -/
theorem connectedLanguage_mem_PSPACE :
    ConnectedLanguage ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits :=
  AbstractBridge.connected_upper_bound

/-! ## Point connectivity -/

/-- Reachable endpoint pairs describe two unique points joined by a continuous
path inside the solution set of `p`. Mathlib's root-level `Path x y` is a
continuous map from `[0,1]` with endpoints `x` and `y`. The endpoints may be
irrational; each endpoint formula must have a singleton solution set. -/
def ReachableEndpoints {n : ℕ} (p : Formula n) : Set (Formula n × Formula n) :=
  {(a, b) | ∃ x y, a.solutionSet = {x} ∧ b.solutionSet = {y} ∧
    ∃ γ : _root_.Path x y, ∀ t, γ t ∈ p.solutionSet}

/-- Point connectivity applies the input encoding to reachable endpoint pairs. -/
def PointLanguage : Set (List Bool) :=
  ⋃ n, ⋃ p : Formula n, (fun (a, b) =>
    Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary (Turing.MultiTapeTM.encList encoding)
      (n, [p.tokens, a.tokens, b.tokens])) '' ReachableEndpoints p

/-- Theorem (Canny, 1988): path connectivity between two formula-described points
in an integer semialgebraic set is in PSPACE, including endpoint validation. -/
theorem pointLanguage_mem_PSPACE :
    PointLanguage ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits :=
  AbstractBridge.point_upper_bound

end LeanCanny.Abstract
