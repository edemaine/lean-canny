/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteLeafPathContext
public import LeanCanny.Algebra.CanonicalPairSpace
public import LeanCanny.Algebra.RationalCoordinatePathSpace

/-! # Native whole-path coordinates for finite-tree leaves

The two indexed stage readers are the canonical pair readers at the queried
parents. Degree and mass controls come from the original finite source.
No intermediate coordinate readers or exact-degree oracles are supplied.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteLeafCoordinateBits
open Polynomial UnivariateRational
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)
open FiniteLeafPathContext
open scoped Classical

noncomputable def rawCoordinate (B : Family) (count : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0) (p : List Bool) : Coordinate :=
  if right count p then CanonicalPairBits.rightCoordinate B count hne (parent count p)
  else CanonicalPairBits.leftCoordinate B count hne (parent count p)

theorem raw_normalized (B : Family) (count : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0) (p : List Bool) :
    rawCoordinate B count hne (pair (pairFst p) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd p)))) = rawCoordinate B count hne p := by
  have hp : position count (pair (pairFst p) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd p)))) = position count p := by
    simp only [position, stage, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hr : right count (pair (pairFst p) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd p)))) ↔ right count p := by
    unfold right
    rw [hp]
  have hpar : parent count (pair (pairFst p) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd p)))) = parent count p := by
    unfold parent
    rw [hp]
    simp only [stage, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold rawCoordinate
  by_cases h : right count p
  · rw [ite_eq_left (hr.mpr h), ite_eq_left h, hpar]
  · rw [ite_eq_right (fun hq => h (hr.mp hq)), ite_eq_right h, hpar]

def degreeControl (count D b : List Bool → ℕ) (u : List Bool) : ℕ := CanonicalPairBits.degreeBudget count D b (leafContext u)
def massControl (count D b : List Bool → ℕ) (u : List Bool) : ℕ := CanonicalPairBits.massBudget count D b (leafContext u)

theorem degreeControl_binary {count D b : List Bool → ℕ} (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    BinaryFn (degreeControl count D b) := (CanonicalPairBits.degreeBudget_binary hn hD hb).comp leafContext_FP

theorem massControl_binary {count D b : List Bool → ℕ} (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    BinaryFn (massControl count D b) := (CanonicalPairBits.massBudget_binary hn hD hb).comp leafContext_FP

theorem coordinateDegree_binary {count D b : List Bool → ℕ} (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    BinaryFn (fun u => degreeControl count D b u ^ depth count u) :=
  RationalCoordinatePath.degreeBudget_binary (degreeControl_binary hn hD hb) (depth_unary hn)

theorem coordinateMass_binary {count D b : List Bool → ℕ} (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    BinaryFn (fun u => depth count u * degreeControl count D b u ^ depth count u * massControl count D b u) :=
  RationalCoordinatePath.massBudget_binary (degreeControl_binary hn hD hb) (massControl_binary hn hD hb) (depth_unary hn)

theorem degreeControl_pos (count D b : List Bool → ℕ) (u : List Bool) : 1 ≤ degreeControl count D b u := by
  have h := CanonicalPairBits.heightBudget_ge_four count D b (leafContext u)
  exact Nat.one_le_pow _ _ (by omega)

theorem parent_budgets (count D b : List Bool → ℕ) (p : List Bool) :
    CanonicalPairBits.degreeBudget count D b (parent count p) = degreeControl count D b (pairFst p) ∧
    CanonicalPairBits.massBudget count D b (parent count p) = massControl count D b (pairFst p) := by
  simp only [degreeControl, massControl, CanonicalPairBits.degreeBudget, CanonicalPairBits.massBudget,
    CanonicalNodeBits.heightBudget, parent, leafContext, BalancedParameterContext.original_packet, and_self]

noncomputable def source (B : Family) (count D b : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0) : RationalCoordinatePathBits.Source where
  inner u s := rawCoordinate B count hne (pair u (BinaryNatCode.encode s))
  degree := degreeControl count D b
  depth := depth count

noncomputable def coordinate (B : Family) (count D b : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0) : List Bool → Coordinate :=
  (source B count D b hne).coordinate

variable (B : Family) (count D b : List Bool → ℕ)
variable (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
variable (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
variable (hheight : ∀ c i, i < count c → B.height (pair c (BinaryNatCode.encode i)) ≤ b c)

attribute [local irreducible] CanonicalNodeBits.node

include hdegree hheight in
theorem raw_bounds (p : List Bool) :
    (rawCoordinate B count hne p).degree ≤ degreeControl count D b (pairFst p) ∧
    coefficientMass (rawCoordinate B count hne p).numerator ≤ 2 ^ massControl count D b (pairFst p) ∧
    coefficientMass (rawCoordinate B count hne p).denominator ≤ 2 ^ massControl count D b (pairFst p) := by
  have hd := CanonicalPairBits.coordinate_degrees B count D b hne hdegree hheight (parent count p)
  have hm := CanonicalPairBits.coordinate_mass B count D b hne hdegree hheight (parent count p)
  rw [(parent_budgets count D b p).1] at hd
  rw [(parent_budgets count D b p).2] at hm
  unfold rawCoordinate
  split_ifs
  · exact ⟨hd.2, hm.2.1, hm.2.2⟩
  · exact ⟨hd.1, hm.1, hm.2.2⟩

include hdegree hheight in
theorem stage_bounds (u : List Bool) (s : ℕ) :
    ((source B count D b hne).inner u s).degree ≤ degreeControl count D b u ∧
    coefficientMass ((source B count D b hne).inner u s).numerator ≤ 2 ^ massControl count D b u ∧
    coefficientMass ((source B count D b hne).inner u s).denominator ≤ 2 ^ massControl count D b u := by
  simpa only [source, pairFst_pair] using raw_bounds B count D b hne hdegree hheight (pair u (BinaryNatCode.encode s))

include hdegree hheight in
theorem stageEvaluators (A : Readers B) (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    SpaceFunction (PrimitivePairBits.coefficient (RationalCoordinatePathBits.indexedNumerator (source B count D b hne))) ∧
    SpaceFunction (PrimitivePairBits.coefficient (RationalCoordinatePathBits.indexedDenominator (source B count D b hne))) := by
  have E := CanonicalPairBits.coordinateEvaluators B count D b hne hdegree hheight A hn hD hb
  have Q := SpaceFunction.ofFP _ (parent_FP hn)
  have EL := PrimitivePairBits.withContextEvaluator _ (parent count) Q E.1
  have ER := PrimitivePairBits.withContextEvaluator _ (parent count) Q E.2.1
  have ED := PrimitivePairBits.withContextEvaluator _ (parent count) Q E.2.2
  have hp := (right_fppred hn).comp RationalSubstitution.IntegerBits.context_mem_FP
  have EN := SpaceFunction.branch (fun q => decide (right count (RationalSubstitution.IntegerBits.context q))) hp.flag_mem_FP ER EL
  constructor
  · exact EN.congr (funext fun q => by
      simp only [Function.comp_apply, PrimitivePairBits.coefficient, RationalCoordinatePathBits.indexedNumerator, source, raw_normalized]
      by_cases h : right count (RationalSubstitution.IntegerBits.context q) <;>
        simp only [rawCoordinate, h, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false])
  · exact ED.congr (funext fun q => by
      simp only [Function.comp_apply, PrimitivePairBits.coefficient, RationalCoordinatePathBits.indexedDenominator, source, raw_normalized]
      by_cases h : right count (RationalSubstitution.IntegerBits.context q) <;> simp only [rawCoordinate, h, ite_true, ite_false]
      rfl)

include hdegree hheight in
theorem coefficientEvaluators (A : Readers B) (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    SpaceFunction (PrimitivePairBits.coefficient (fun u => (coordinate B count D b hne u).numerator)) ∧
    SpaceFunction (PrimitivePairBits.coefficient (fun u => (coordinate B count D b hne u).denominator)) := by
  have E := stageEvaluators B count D b hne hdegree hheight A hn hD hb
  exact RationalCoordinatePathBits.coefficientEvaluators (source B count D b hne)
    (degreeControl_binary hn hD hb) (depth_unary hn) E.1 E.2

include hdegree hheight in
theorem coordinate_bounds (u : List Bool) :
    (coordinate B count D b hne u).degree ≤ degreeControl count D b u ^ depth count u ∧
    coefficientMass (coordinate B count D b hne u).numerator ≤ 2 ^ (depth count u * degreeControl count D b u ^ depth count u * massControl count D b u) ∧
    coefficientMass (coordinate B count D b hne u).denominator ≤ 2 ^ (depth count u * degreeControl count D b u ^ depth count u * massControl count D b u) := by
  have H := stage_bounds B count D b hne hdegree hheight u
  exact ⟨RationalCoordinatePath.degree_bound _ _ (fun s => (H s).1) _,
    RationalCoordinatePath.mass_bound _ _ _ (degreeControl_pos count D b u) (fun s => (H s).1)
      (fun s => (H s).2.1) (fun s => (H s).2.2) _⟩

end LeanCanny.Algebra.FiniteLeafCoordinateBits
