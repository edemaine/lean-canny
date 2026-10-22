/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableScaling

/-! # The actual integer preparation supplies a valid symbolic table

Leaves are integer denominator-cleared dyadic originals, processed by the
existing integer scaled-squarefree construction. Every internal direction is
the existing integer last-success selection. Source-derived uniform bounds
show that this concrete table works over the symbolic coefficient field.
No symbolic separability or GCD-order oracle is an input.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTable
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open scoped Classical

noncomputable def integerDirections (a : ℕ → SeparableIntegerPolynomial) (h i : ℕ) : ℕ :=
  PrimitivePair.select (BalancedPrimitiveTree.node a h (2 * i)).polynomial
    (BalancedPrimitiveTree.node a h (2 * i + 1)).polynomial

theorem integer_node_eq (a : ℕ → SeparableIntegerPolynomial) (h i : ℕ) :
    node (fun i => (a i).polynomial) (integerDirections a) h i = (BalancedPrimitiveTree.node a h i).polynomial := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih => simp only [node, ih, BalancedPrimitiveTree.node, SeparableIntegerPolynomial.combine, integerDirections]

theorem integer_node_degree (B : Budget) (a : ℕ → SeparableIntegerPolynomial)
    (ha : ∀ i, (a i).polynomial.natDegree ≤ B.degree) (h i : ℕ) :
    (BalancedPrimitiveTree.node a h i).polynomial.natDegree ≤ (treeBudget B h).degree := by
  induction h generalizing i with
  | zero => exact ha i
  | succ h ih =>
    rw [BalancedPrimitiveTree.node, SeparableIntegerPolynomial.combine_degree]
    exact Nat.mul_le_mul (ih (2 * i)) (ih (2 * i + 1))

theorem integerDirections_admissible (B : Budget) (a : ℕ → SeparableIntegerPolynomial)
    (ha : ∀ i, (a i).polynomial.natDegree ≤ B.degree) : Admissible B (integerDirections a) := by
  intro h i
  have hs := (PrimitivePair.select_spec
    (BalancedPrimitiveTree.node a h (2 * i)).polynomial
    (BalancedPrimitiveTree.node a h (2 * i + 1)).polynomial
    ((BalancedPrimitiveTree.node a h (2 * i)).separable_in_field (L := AlgebraicClosure ℚ))
    ((BalancedPrimitiveTree.node a h (2 * i + 1)).separable_in_field (L := AlgebraicClosure ℚ))
    (IsAlgClosed.splits _) (IsAlgClosed.splits _)).1
  exact hs.trans (Nat.pow_le_pow_left (Nat.mul_le_mul
    (integer_node_degree B a ha h (2 * i)) (integer_node_degree B a ha h (2 * i + 1))) _)

theorem node_map_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (a : ℕ → R[X]) (c : ℕ → ℕ → ℕ) (h i : ℕ) :
    (node a c h i).map f = node (fun i => (a i).map f) c h i := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih => rw [node, CoordinateRecoveryMap.resultant f hf, ih, ih]; rfl

noncomputable def integerLeaves (B : Budget) (a : ℕ → Polynomial Coefficient)
    (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0) (s : ℕ) (hs : B.testExponent ≤ s)
    (i : ℕ) : SeparableIntegerPolynomial :=
  SeparableIntegerPolynomial.squarefree (clear (a i) B.innerDegree s) (B.clear_ne_zero _ (ha i) (hn i) s hs)

theorem integerLeaves_degree (B : Budget) (a : ℕ → Polynomial Coefficient)
    (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0) (s : ℕ) (hs : B.testExponent ≤ s) (i : ℕ) :
    (integerLeaves B a ha hn s hs i).polynomial.natDegree ≤ B.squarefree.degree := by
  exact (ScaledSquarefree.polynomial_natDegree_le _ (B.clear_ne_zero _ (ha i) (hn i) s hs)).trans
    ((B.cleared_degree _ (ha i) s hs).le.trans (ha i).1)

def preparationExponent (B : Budget) (height : ℕ) : ℕ :=
  B.testExponent + referenceExponent B.squarefree height

noncomputable def preparedLeaves (B : Budget) (a : ℕ → Polynomial Coefficient)
    (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0) (height : ℕ) : ℕ → SeparableIntegerPolynomial :=
  integerLeaves B a ha hn (preparationExponent B height) (Nat.le_add_right _ _)

noncomputable def preparedDirections (B : Budget) (a : ℕ → Polynomial Coefficient)
    (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0) (height : ℕ) : ℕ → ℕ → ℕ :=
  integerDirections (preparedLeaves B a ha hn height)

theorem preparedDirections_admissible (B : Budget) (a : ℕ → Polynomial Coefficient)
    (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0) (height : ℕ) :
    Admissible B.squarefree (preparedDirections B a ha hn height) :=
  integerDirections_admissible _ _ (integerLeaves_degree B a ha hn _ _)

theorem prepared_node_associated (B : Budget) (a : ℕ → Polynomial Coefficient)
    (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0) (height h i : ℕ) (hh : h ≤ height) :
    Associated
      ((node (fun i => SymbolicScaledSquarefree.polynomial (a i))
        (preparedDirections B a ha hn height) h i).map
          (scalarEvaluation (InfinitesimalSign.dyadic (preparationExponent B height))))
      ((BalancedPrimitiveTree.node (preparedLeaves B a ha hn height) h i).polynomial.map (Int.castRingHom ℝ)) := by
  have hsymbol (i : ℕ) : B.squarefree.Controls (SymbolicScaledSquarefree.polynomial (a i)) :=
    B.squarefree_controls _ (ha i)
  have he : InfinitesimalSign.dyadic (preparationExponent B height) ≤
      InfinitesimalSign.dyadic (referenceExponent B.squarefree height) :=
    dyadic_antitone (Nat.le_add_left _ _)
  rw [node_map B.squarefree _ _ hsymbol (preparedDirections_admissible B a ha hn height)
    height h i hh _ (by unfold InfinitesimalSign.dyadic; positivity) he,
    ← integer_node_eq, node_map_injective (Int.castRingHom ℝ) (show Function.Injective (Int.castRingHom ℝ) from Int.cast_injective)]
  exact node_associated _ _ _ (fun i =>
    (B.cleared_squarefree_associated _ (ha i) (hn i) _ (Nat.le_add_right _ _)).symm) h i

theorem prepared_node_generic_separable (B : Budget) (a : ℕ → Polynomial Coefficient)
    (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0) (height h i : ℕ) (hh : h ≤ height) :
    ((node (fun i => SymbolicScaledSquarefree.polynomial (a i))
      (preparedDirections B a ha hn height) h i).map embedding).Separable := by
  have hassoc := prepared_node_associated B a ha hn height h i hh
  have hs := hassoc.symm.separable
    ((BalancedPrimitiveTree.node (preparedLeaves B a ha hn height) h i).separable_in_field (L := ℝ))
  have hne : node (fun i => SymbolicScaledSquarefree.polynomial (a i))
      (preparedDirections B a ha hn height) h i ≠ 0 := by
    intro hz
    rw [hz, Polynomial.map_zero] at hs
    exact hs.ne_zero rfl
  exact (node_separable_iff B.squarefree _ _ (fun i => B.squarefree_controls _ (ha i))
    (preparedDirections_admissible B a ha hn height) height h i hh hne _
    (by unfold InfinitesimalSign.dyadic; positivity)
    (dyadic_antitone (Nat.le_add_left _ _))).mp hs

theorem prepared_node_degree (B : Budget) (a : ℕ → Polynomial Coefficient)
    (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0) (height h i : ℕ) (hh : h ≤ height) :
    (BalancedPrimitiveTree.node (preparedLeaves B a ha hn height) h i).polynomial.natDegree =
      (node (fun i => SymbolicScaledSquarefree.polynomial (a i))
        (preparedDirections B a ha hn height) h i).natDegree := by
  have hd := PrincipalSubresultant.natDegree_eq_of_associated (prepared_node_associated B a ha hn height h i hh)
  rw [natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℝ) from Int.cast_injective)] at hd
  have hs := node_degree_map B.squarefree (fun i => SymbolicScaledSquarefree.polynomial (a i))
    (preparedDirections B a ha hn height) (fun i => B.squarefree_controls _ (ha i))
    (preparedDirections_admissible B a ha hn height) height h i hh
    (InfinitesimalSign.dyadic (preparationExponent B height))
    (by unfold InfinitesimalSign.dyadic; positivity) (dyadic_antitone (Nat.le_add_left _ _))
  exact hd.symm.trans hs

end LeanCanny.Algebra.SymbolicFixedTable
