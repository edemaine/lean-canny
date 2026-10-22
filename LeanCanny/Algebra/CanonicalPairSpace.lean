/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CanonicalNodeSpace
public import LeanCanny.Algebra.SpaceDegreePair
public import LeanCanny.Algebra.PreprocessedPairCoordinateBounds

/-! # Uniform native pair-coordinate readers at finite-tree nodes

The two children have space-computed exact degrees and residues. Checked
metadata packets feed those computations to the existing canonical pair
construction, without another square-free normalization. At every valid
parent the results are exactly the pair coordinates used by `flat`.
-/

@[expose] public section

namespace LeanCanny.Algebra.CanonicalPairBits
open Polynomial UnivariateRational
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)
open BalancedParameterContext (packet original)

def childQuery (right : Bool) (count : List Bool → ℕ) : List Bool → List Bool :=
  BalancedParameterContext.child right ∘ CanonicalNodeContext.packet count

theorem childQuery_FP (right : Bool) {count : List Bool → ℕ} (hn : UnaryFn count) : childQuery right count ∈ FP :=
  mem_FP_comp (CanonicalNodeContext.packet_FP hn) (BalancedParameterContext.child_FP right)

theorem child_packet (right : Bool) (count : List Bool → ℕ) (c : List Bool) (h i : ℕ)
    (hh : h + 1 ≤ (count c).size) (hi : i < 2 ^ ((count c).size - (h + 1))) :
    childQuery right count (packet c (h + 1) i) = packet c h (2 * i + if right then 1 else 0) := by
  simp only [childQuery, Function.comp_apply, CanonicalNodeContext.packet, BalancedParameterContext.original_packet,
    CanonicalNodeContext.height_packet count c (h + 1) i hh, CanonicalNodeContext.index_packet count c (h + 1) i hh hi,
    BalancedParameterContext.child_packet]

variable (B : Family) (count D b : List Bool → ℕ)
variable (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
variable (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
variable (hheight : ∀ c i, i < count c → B.height (pair c (BinaryNatCode.encode i)) ≤ b c)

noncomputable def leftCoordinate (p : List Bool) : Coordinate :=
  (CanonicalNodeBits.node B count hne (childQuery false count p)).leftCoordinate (CanonicalNodeBits.node B count hne (childQuery true count p))

noncomputable def rightCoordinate (p : List Bool) : Coordinate :=
  (CanonicalNodeBits.node B count hne (childQuery false count p)).rightCoordinate (CanonicalNodeBits.node B count hne (childQuery true count p))

attribute [local irreducible] CanonicalNodeBits.node BinaryNat.normalize

include hdegree hheight in
theorem coordinateEvaluators (A : Readers B) (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    SpaceFunction (PrimitivePairBits.coefficient (fun p => (leftCoordinate B count hne p).numerator)) ∧
    SpaceFunction (PrimitivePairBits.coefficient (fun p => (rightCoordinate B count hne p).numerator)) ∧
    SpaceFunction (PrimitivePairBits.coefficient (fun p => (leftCoordinate B count hne p).denominator)) := by
  let F := CanonicalNodeBits.family B count D b hne hdegree hheight
  let FL := F.reindex (childQuery false count)
  let FR := F.reindex (childQuery true count)
  have E := CanonicalNodeBits.coefficientEvaluator B count D b hne hdegree hheight A hn hD hb
  have DE := CanonicalNodeBits.degreeEvaluator B count D b hne hdegree hheight A hn hD hb
  have EL : SpaceFunction (PrimitivePairBits.coefficient FL.polynomial) := PrimitivePairBits.withContextEvaluator _
    (childQuery false count) (SpaceFunction.ofFP _ (childQuery_FP false hn)) E
  have ER : SpaceFunction (PrimitivePairBits.coefficient FR.polynomial) := PrimitivePairBits.withContextEvaluator _
    (childQuery true count) (SpaceFunction.ofFP _ (childQuery_FP true hn)) E
  have DL0 := DE.precompose (childQuery false count) (childQuery_FP false hn)
  have DR0 := DE.precompose (childQuery true count) (childQuery_FP true hn)
  have DL : SpaceFunction (fun p => BinaryNatCode.encode (FL.polynomial p).natDegree) := DL0.congr (funext fun _ => rfl)
  have DR : SpaceFunction (fun p => BinaryNatCode.encode (FR.polynomial p).natDegree) := DR0.congr (funext fun _ => rfl)
  have HL : BinaryFn FL.height := (CanonicalNodeBits.heightBudget_binary hn hD hb).comp (childQuery_FP false hn)
  have HR : BinaryFn FR.height := (CanonicalNodeBits.heightBudget_binary hn hD hb).comp (childQuery_FP true hn)
  exact SpaceDegreePair.coordinateEvaluators FL FR EL ER DL DR HL HR
    (fun p => (CanonicalNodeBits.node B count hne (childQuery false count p)).separable_in_field (L := AlgebraicClosure ℚ))
    (fun p => (CanonicalNodeBits.node B count hne (childQuery true count p)).separable_in_field (L := AlgebraicClosure ℚ))

theorem child_node (right : Bool) (c : List Bool) (h i : ℕ)
    (hh : h + 1 ≤ (count c).size) (hi : i < 2 ^ ((count c).size - (h + 1))) :
    CanonicalNodeBits.node B count hne (childQuery right count (packet c (h + 1) i)) =
      BalancedPrimitiveTree.node (PaddedAnnihilatorPreparation.leaves B count hne c) h (2 * i + if right then 1 else 0) := by
  have hi' := BalancedTablePolynomials.child_index_lt (count c).size h i hh hi
  have hic : 2 * i + (if right then 1 else 0) < 2 ^ ((count c).size - h) := by
    cases right with
    | false => simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using hi'.1
    | true => exact hi'.2
  rw [child_packet right count c h i hh hi]
  simp only [CanonicalNodeBits.node, BalancedParameterContext.original_packet,
    CanonicalNodeContext.height_packet count c h _ (by omega), CanonicalNodeContext.index_packet count c h _ (by omega) hic]

theorem left_packet (c : List Bool) (h i : ℕ) (hh : h + 1 ≤ (count c).size) (hi : i < 2 ^ ((count c).size - (h + 1))) :
    leftCoordinate B count hne (packet c (h + 1) i) =
      (BalancedPrimitiveTree.node (PaddedAnnihilatorPreparation.leaves B count hne c) h (2 * i)).leftCoordinate
        (BalancedPrimitiveTree.node (PaddedAnnihilatorPreparation.leaves B count hne c) h (2 * i + 1)) := by
  simp only [leftCoordinate, child_node B count hne false c h i hh hi, child_node B count hne true c h i hh hi,
    Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]

theorem right_packet (c : List Bool) (h i : ℕ) (hh : h + 1 ≤ (count c).size) (hi : i < 2 ^ ((count c).size - (h + 1))) :
    rightCoordinate B count hne (packet c (h + 1) i) =
      (BalancedPrimitiveTree.node (PaddedAnnihilatorPreparation.leaves B count hne c) h (2 * i)).rightCoordinate
        (BalancedPrimitiveTree.node (PaddedAnnihilatorPreparation.leaves B count hne c) h (2 * i + 1)) := by
  simp only [rightCoordinate, child_node B count hne false c h i hh hi, child_node B count hne true c h i hh hi,
    Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]

theorem flat_step (c : List Bool) (h i j : ℕ) (hh : h + 1 ≤ (count c).size) (hi : i < 2 ^ ((count c).size - (h + 1))) :
    BalancedPrimitiveTree.flat (PaddedAnnihilatorPreparation.leaves B count hne c) (h + 1) i j =
      if j < 2 ^ h then
        (BalancedPrimitiveTree.flat (PaddedAnnihilatorPreparation.leaves B count hne c) h (2 * i) j).comp
          (leftCoordinate B count hne (packet c (h + 1) i))
      else (BalancedPrimitiveTree.flat (PaddedAnnihilatorPreparation.leaves B count hne c) h (2 * i + 1) (j - 2 ^ h)).comp
          (rightCoordinate B count hne (packet c (h + 1) i)) := by
  rw [left_packet B count hne c h i hh hi, right_packet B count hne c h i hh hi]
  rfl

theorem child_height (right : Bool) (p : List Bool) :
    CanonicalNodeBits.heightBudget count D b (childQuery right count p) = CanonicalNodeBits.heightBudget count D b p := by
  simp only [CanonicalNodeBits.heightBudget, childQuery, Function.comp_apply, BalancedParameterContext.original_child,
    CanonicalNodeContext.packet, BalancedParameterContext.original_packet]

include hdegree hheight in
theorem child_bounds (right : Bool) (p : List Bool) :
    (CanonicalNodeBits.node B count hne (childQuery right count p)).polynomial.natDegree ≤ CanonicalNodeBits.heightBudget count D b p ∧
      coefficientMass (CanonicalNodeBits.node B count hne (childQuery right count p)).polynomial ≤ 2 ^ CanonicalNodeBits.heightBudget count D b p := by
  let q := childQuery right count p
  have h := FiniteAnnihilatorTree.source_tree_bounds
    (fun j => B.polynomial (pair (original q) (BinaryNatCode.encode j))) (count (original q)) (hne (original q))
    (D (original q)) (b (original q)) (hdegree (original q)) (fun j hj k => (B.coefficient_bound _ k).trans
      (Nat.pow_le_pow_right (by decide) (hheight (original q) j hj)))
    (CanonicalNodeContext.height count q) (CanonicalNodeContext.index count q) (CanonicalNodeContext.height_le count q)
  have hd : (CanonicalNodeBits.node B count hne q).polynomial.natDegree ≤ CanonicalNodeBits.heightBudget count D b q := by
    simpa only [CanonicalNodeBits.node, CanonicalNodeBits.heightBudget, PaddedAnnihilatorPreparation.leaves] using h.parameterDegree
  have hm : coefficientMass (CanonicalNodeBits.node B count hne q).polynomial ≤ 2 ^ CanonicalNodeBits.heightBudget count D b q := by
    simpa only [CanonicalNodeBits.node, CanonicalNodeBits.heightBudget, PaddedAnnihilatorPreparation.leaves] using h.parameterMass
  dsimp only [q] at hd hm
  rw [child_height count D b right p] at hd hm
  exact ⟨hd, hm⟩

def degreeBudget (count D b : List Bool → ℕ) (p : List Bool) : ℕ := (CanonicalNodeBits.heightBudget count D b p) ^ 3
def massBudget (count D b : List Bool → ℕ) (p : List Bool) : ℕ := (CanonicalNodeBits.heightBudget count D b p) ^ 10

theorem degreeBudget_binary {count D b : List Bool → ℕ} (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    BinaryFn (degreeBudget count D b) := (CanonicalNodeBits.heightBudget_binary hn hD hb).powUnary (UnaryFn.const 3)

theorem massBudget_binary {count D b : List Bool → ℕ} (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    BinaryFn (massBudget count D b) := (CanonicalNodeBits.heightBudget_binary hn hD hb).powUnary (UnaryFn.const 10)

theorem heightBudget_ge_four (count D b : List Bool → ℕ) (p : List Bool) : 4 ≤ CanonicalNodeBits.heightBudget count D b p := by
  have hp : 0 < 256 * (count (original p) + 1) ^ 4 := by positivity
  have he : 1 ≤ 256 * (count (original p) + 1) ^ 4 := by omega
  calc
    4 ≤ D (original p) + b (original p) + 4 := by omega
    _ = (D (original p) + b (original p) + 4) ^ 1 := (pow_one _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) he

include hdegree hheight in
theorem coordinate_degrees (p : List Bool) :
    (leftCoordinate B count hne p).degree ≤ degreeBudget count D b p ∧
      (rightCoordinate B count hne p).degree ≤ degreeBudget count D b p :=
  SeparableIntegerPolynomial.coordinates_degree_uniform _ _ _ (heightBudget_ge_four count D b p)
    (child_bounds B count D b hne hdegree hheight false p).1 (child_bounds B count D b hne hdegree hheight true p).1

include hdegree hheight in
theorem coordinate_mass (p : List Bool) :
    coefficientMass (leftCoordinate B count hne p).numerator ≤ 2 ^ massBudget count D b p ∧
    coefficientMass (rightCoordinate B count hne p).numerator ≤ 2 ^ massBudget count D b p ∧
    coefficientMass (leftCoordinate B count hne p).denominator ≤ 2 ^ massBudget count D b p :=
  SeparableIntegerPolynomial.coordinates_mass_uniform _ _ _ (heightBudget_ge_four count D b p)
    (child_bounds B count D b hne hdegree hheight false p).1 (child_bounds B count D b hne hdegree hheight true p).1
    (child_bounds B count D b hne hdegree hheight false p).2 (child_bounds B count D b hne hdegree hheight true p).2

end LeanCanny.Algebra.CanonicalPairBits
