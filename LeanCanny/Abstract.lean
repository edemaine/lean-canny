/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Path

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Policy.BinaryIntUnaryFin
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy
public import CslibFrontier.Computability.Complexity.Classes.Space
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair

public import LeanCanny.AbstractBridge
public import LeanCanny.CountingHierarchy.AbstractBridge

/-! # A formal abstract of real-algebraic complexity bounds

This file introduces integer polynomial expressions, their real solution sets,
and a shared binary encoding. It proves ETR ∈ PSPACE, ∃ℝ ⊆ PSPACE, and PSPACE
bounds for semialgebraic connectivity following Canny (1988). It also proves
ETR ∈ C₂₆P, ∃ℝ ⊆ C₂₆P, and ∃∀ℝ ∈ C₆₀P following OpenAI (2026).

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

## References

* John F. Canny, *Some Algebraic and Geometric Computations in PSPACE*.
  Technical Report UCB/CSD-88-439, University of California, Berkeley, August 1988.
  https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/6041.html
* John F. Canny, *Some Algebraic and Geometric Computations in PSPACE*.
  Proceedings of the 20th Annual ACM Symposium on Theory of Computing (STOC ’88),
  ACM, 1988, pp. 460–467. https://doi.org/10.1145/62212.62257
* OpenAI, *Existential–universal real sentences in the counting hierarchy*.
  OpenAI Math Release preprint, October 4, 2026.
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/etr-counting-hierarchy.pdf
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

/-- Evaluate an integer polynomial expression at a real assignment `x`. -/
def Term.eval {n : ℕ} (x : Fin n → ℝ) : Term n → ℝ
  | .const z => z
  | .var i => x i
  | .add a b => a.eval x + b.eval x
  | .mul a b => a.eval x * b.eval x

/-- A Boolean formula compares polynomial expressions with zero, using equality
or strict inequality, and combines these assertions by negation, conjunction,
and disjunction. ETR existentially quantifies all occurring variables;
connectivity treats them as coordinates of the described space. -/
inductive Formula (n : ℕ) where
  | false : Formula n
  | eqZero : Term n → Formula n
  | ltZero : Term n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n

/-- A formula describes a solution set in `ℝⁿ`, represented by `Fin n → ℝ`.
Negation, conjunction, and disjunction give complement, intersection, and union. -/
def Formula.solutionSet {n : ℕ} : Formula n → Set (Fin n → ℝ)
  | .false => ∅
  | .eqZero t => {x | t.eval x = 0}
  | .ltZero t => {x | t.eval x < 0}
  | .not p => p.solutionSetᶜ
  | .and p q => p.solutionSet ∩ q.solutionSet
  | .or p q => p.solutionSet ∪ q.solutionSet

/-! ## Binary input convention

CSLib Frontier’s `derive_encoding` command generates a flat constructor stream
for each syntax type. Integer coefficients use binary encoding and variable
indices use unary encoding.
Opening the named policy scope selects these field encodings; the formula
encoding reuses the term encoding. Constructor tokens are framed individually;
comparison tokens carry complete term words. Dimensions are unary; query framing
has fixed depth.

Each language below consists of the encodings of its valid mathematical inputs
and rejects every other bitstring. For a set `S` and encoding function `f`,
`S.image f` is the set of encoded values `f x` for `x ∈ S`.
-/

open scoped Turing.MultiTapeTM.EncodingPolicy.BinaryIntUnaryFin

derive_encoding encTerm (n : ℕ) : Term n
derive_encoding encFormula (n : ℕ) : Formula n

/-! ## ∃ℝ -/

/-- ETR consists of the encodings of real-satisfiable formulas. -/
def ETR : Set (List Bool) :=
  ⋃ n, {p : Formula n | p.solutionSet.Nonempty}.image (encFormula n)

/-- Theorem (Canny, 1988): existential real satisfiability is decidable in deterministic
polynomial space, including rejection of malformed binary inputs. -/
theorem etr_in_PSPACE : ETR ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits := by
  bridge_bound AbstractBridge.etr_upper_bound

/-- Theorem (OpenAI, 2026): ETR belongs to the fixed counting level C₂₆P,
with the same encoded language used in the PSPACE theorem above. -/
theorem etr_in_CountingLevel :
    ETR ∈ Cslib.Complexity.CountingLevel 26 Turing.MultiTapeTM.encBits := by
  bridge_bound CountingHierarchy.AbstractBridge.etr_upper_bound

/-- The class ∃ℝ consists of binary languages reducible to ETR in polynomial time.
A reduction is a polynomial-time algorithm on all input strings that preserves
yes/no answers; the background library's `PolyTimeReducible` includes its time bound. -/
def ExistsReal : Set (Set (List Bool)) :=
  {L | Cslib.Complexity.PolyTimeReducible Turing.MultiTapeTM.encBits
    Turing.MultiTapeTM.encBits L ETR}

/-- Corollary (Canny, 1988): every problem in ∃ℝ is decidable in deterministic
polynomial space. -/
theorem existsReal_subset_PSPACE :
    ExistsReal ⊆ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits :=
  AbstractBridge.existsReal_upper_bound

/-- Corollary (OpenAI, 2026): every problem in ∃ℝ belongs to that same fixed
counting level. -/
theorem existsReal_subset_CountingLevel :
    ExistsReal ⊆ Cslib.Complexity.CountingLevel 26 Turing.MultiTapeTM.encBits :=
  CountingHierarchy.AbstractBridge.existsReal_upper_bound

/-! ## ∃∀ℝ -/

/-- The ∃∀ℝ solution set contains the existential assignments `x` of length `r`
for which every universal assignment `y` of length `s` satisfies `p`.
`Fin.addCases` concatenates the tuples, with the existential coordinates first.
Either block may be empty; nonemptiness of this set expresses ∃∀ℝ truth. -/
def Formula.existsForallSolutionSet {r s : ℕ} (p : Formula (r + s)) : Set (Fin r → ℝ) :=
  {x | ∀ y : Fin s → ℝ, Fin.addCases x y ∈ p.solutionSet}

/-- The language ∃∀ℝ consists of true existential-universal real sentences.
It uses the same formula encoding as ETR and records the unary existential block
length. The union allows all finite block sizes; unused coordinates do not affect
truth. Every other word is rejected. -/
def ExistsForallReal : Set (List Bool) :=
  ⋃ r, ⋃ s, {p : Formula (r + s) | p.existsForallSolutionSet.Nonempty}.image (fun p =>
    Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encBits
      (r, encFormula (r + s) p))

/-- Theorem (OpenAI, 2026): ∃∀ℝ belongs to CH.
This formalization supplies the fixed level C₆₀P, independent of variable counts,
polynomial degrees, and coefficient magnitudes. -/
theorem existsForallReal_in_CountingLevel :
    ExistsForallReal ∈ Cslib.Complexity.CountingLevel 60 Turing.MultiTapeTM.encBits := by
  bridge_bound CountingHierarchy.AbstractBridge.twoBlock_upper_bound

/-! ## Whole-space connectivity -/

/-- Connected formulas describe connected solution sets in `ℝⁿ`, allowing the
empty set (Mathlib's root-level `IsPreconnected`). -/
def ConnectedFormulas (n : ℕ) : Set (Formula n) :=
  {p | _root_.IsPreconnected p.solutionSet}

/-- Whole-space connectivity applies the input encoding to connected formulas. -/
def ConnectedLanguage : Set (List Bool) :=
  ⋃ n, (ConnectedFormulas n).image (fun p =>
    Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encBits
      (n, encFormula n p))

/-- Theorem (Canny, 1988): connectivity of an integer semialgebraic set is in PSPACE,
including singular and unbounded sets and accepting the empty set. -/
theorem connectedLanguage_in_PSPACE :
    ConnectedLanguage ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits := by
  bridge_bound AbstractBridge.connected_upper_bound

/-! ## Point reachability -/

/-- Reachable endpoint pairs describe two unique points joined by a continuous
path inside the solution set of `p`. Mathlib's root-level `Path x y` is a
continuous map from `[0,1]` with endpoints `x` and `y`. The endpoints may be
irrational; each endpoint formula must have a singleton solution set. -/
def ReachableEndpoints {n : ℕ} (p : Formula n) : Set (Formula n × Formula n) :=
  {(a, b) | ∃ x y, a.solutionSet = {x} ∧ b.solutionSet = {y} ∧
    ∃ γ : _root_.Path x y, ∀ t, γ t ∈ p.solutionSet}

/-- Reachability applies the input encoding to reachable endpoint pairs. -/
def ReachableLanguage : Set (List Bool) :=
  ⋃ n, ⋃ p : Formula n, (ReachableEndpoints p).image (fun (a, b) =>
    Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary
      (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encBits)
      (n, [encFormula n p, encFormula n a, encFormula n b]))

/-- Theorem (Canny, 1988): path connectivity between two formula-described points
in an integer semialgebraic set is in PSPACE, including endpoint validation. -/
theorem reachableLanguage_in_PSPACE :
    ReachableLanguage ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits := by
  bridge_bound AbstractBridge.point_upper_bound

end LeanCanny.Abstract
