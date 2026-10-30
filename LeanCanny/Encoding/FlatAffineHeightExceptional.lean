/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineHeightValueBounds
public import LeanCanny.Algebra.UniformSquarefreeExceptionalSpace

/-! # Native exceptional factors of the actual varying-height coordinates

The original signed-record source supplies every principal factor. Binary
counts and budgets suffice even when the principal range is exponential.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineHeightExceptional
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def degree (F : Inputs) (z : List Bool) : ℕ :=
  FlatAffineHeightValues.coordinateDegree F (pairFst z)

noncomputable def exponent (F : Inputs) (z : List Bool) : ℕ :=
  FlatAffineHeightValueBounds.coordinateExponent F (pairFst z)

theorem degree_binary {F : Inputs} (h : F.Access) : BinaryFn (degree F) :=
  (FlatAffineHeightValues.coordinateDegree_binary h).comp pairFst_mem_FP

theorem exponent_binary {F : Inputs} (h : F.Access) : BinaryFn (exponent F) :=
  (FlatAffineHeightValueBounds.coordinateExponent_binary h).comp pairFst_mem_FP

theorem indexed_degree_le (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    (FlatAffineHeightGrid.indexed F height z).natDegree ≤ degree F z := by
  rw [FlatAffineHeightGrid.indexed, FlatAffineHeightGrid.coordinate_comp]
  apply Geometry.AffineShiftCoordinates.coordinate_degree_le _ _ _ _ |>.trans_eq
  exact congrArg (fun n => n + 1) (FlatAffineHeightValues.dimension_eq F (pairFst z)).symm

theorem indexed_degree_eq (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    (FlatAffineHeightGrid.indexed F height z).natDegree = degree F z := by
  rw [FlatAffineHeightGrid.indexed, FlatAffineHeightGrid.coordinate_comp]
  exact FlatAffineHeightValues.coordinate_degree_eq F hcone height _ _

theorem indexed_inner_le (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) (k : ℕ) :
    ((FlatAffineHeightGrid.indexed F height z).coeff k).natDegree ≤ degree F z := by
  rw [FlatAffineHeightGrid.indexed, FlatAffineHeightGrid.coordinate_comp]
  exact FlatAffineHeightValues.coordinate_inner_bound F height _ _ k

theorem indexed_mass_le (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) (k : ℕ) :
    coefficientMass ((FlatAffineHeightGrid.indexed F height z).coeff k) ≤ 2 ^ exponent F z := by
  apply (NestedMass.coeff_le _ _).trans
  rw [FlatAffineHeightGrid.indexed, FlatAffineHeightGrid.coordinate_comp]
  exact FlatAffineHeightValueBounds.coordinate_mass_bound F height _ _

noncomputable def indexed (F : Inputs) (height : (u : List Bool) → Fin (count F u)) : List Bool → Polynomial ℤ :=
  UniformSquarefreeExceptionalBits.polynomial (FlatAffineHeightGrid.indexed F height) (degree F)

theorem indexedEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (PrimitivePairBits.coefficient (indexed F height)) :=
  UniformSquarefreeExceptionalBits.evaluator (FlatAffineHeightGrid.indexedReader h height hh)
    (degree_binary h) (degree_binary h) (exponent_binary h)
    (indexed_degree_le F height) (indexed_inner_le F height) (indexed_mass_le F height)

theorem indexed_ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (z : List Bool) : indexed F height z ≠ 0 := by
  apply UniformSquarefreeExceptionalBits.ne_zero _ _ (indexed_degree_eq F hcone height) ?_ z
  intro c
  apply Polynomial.ne_zero_of_natDegree_gt
  rw [indexed_degree_eq F hcone height]
  exact Nat.zero_lt_succ _

lemma indexed_coordinate_eq (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (u : List Bool) (i : Fin (count F u)) :
    FlatAffineHeightGrid.indexed F height (pair u (BinaryNatCode.encode i.val)) =
      FlatAffineHeightGrid.coordinate F height u i := by
  unfold FlatAffineHeightGrid.indexed
  simp only [pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [FlatAffineHeightGrid.coordinate_comp, pairFst_pair, FlatAffineHeightGram.rawRow_val]

theorem indexed_avoids {K : Type*} [Field K] (phi : Polynomial ℤ →+* K)
    (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) (i : Fin (count F u))
    (ht : phi (indexed F height (pair u (BinaryNatCode.encode i.val))) ≠ 0) :
    phi (SymbolicScaledSquarefree.exceptional (FlatAffineHeightGrid.coordinate F height u i)) ≠ 0 := by
  change phi (UniformSquarefreeExceptionalBits.polynomial (FlatAffineHeightGrid.indexed F height)
    (degree F) (pair u (BinaryNatCode.encode i.val))) ≠ 0 at ht
  rw [UniformSquarefreeExceptionalBits.polynomial_eq _ _ (indexed_degree_eq F hcone height),
    indexed_coordinate_eq] at ht
  exact UniformSquarefreeExceptional.avoids_exceptional phi _ ht

noncomputable def polynomial (F : Inputs) (height : (u : List Bool) → Fin (count F u)) : List Bool → Polynomial ℤ :=
  PolynomialFamilyProductBits.polynomial (indexed F height) (count F)

theorem evaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (PrimitivePairBits.coefficient (polynomial F height)) :=
  PolynomialFamilyProductBits.evaluator _ _ (BinaryFn.ofUnary (FlatAffineFullSourcePositive.count_unary h))
    (indexedEvaluator h height hh)

theorem ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) : polynomial F height u ≠ 0 :=
  PolynomialFamilyProductBits.ne_zero _ _ (indexed_ne_zero F hcone height) u

theorem avoids {K : Type*} [Field K] (phi : Polynomial ℤ →+* K)
    (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool)
    (ht : phi (polynomial F height u) ≠ 0) (i : Fin (count F u)) :
    phi (SymbolicScaledSquarefree.exceptional (FlatAffineHeightGrid.coordinate F height u i)) ≠ 0 := by
  apply indexed_avoids phi F hcone height u i
  have H : ∀ j < count F u, phi (indexed F height (pair u (BinaryNatCode.encode j))) ≠ 0 := by
    simpa only [polynomial, PolynomialFamilyProductBits.polynomial, map_prod,
      Finset.prod_ne_zero_iff, Finset.mem_range] using ht
  exact H i.val i.isLt

noncomputable def indexedDegreeBound (F : Inputs) : List Bool → ℕ :=
  UniformSquarefreeExceptionalBits.degreeBound (degree F) (degree F)

noncomputable def indexedMassBound (F : Inputs) : List Bool → ℕ :=
  UniformSquarefreeExceptionalBits.massBound (degree F) (exponent F)

theorem indexedDegreeBound_binary {F : Inputs} (h : F.Access) : BinaryFn (indexedDegreeBound F) :=
  UniformSquarefreeExceptionalBits.degreeBound_binary (degree_binary h) (degree_binary h)

theorem indexedMassBound_binary {F : Inputs} (h : F.Access) : BinaryFn (indexedMassBound F) :=
  UniformSquarefreeExceptionalBits.massBound_binary (degree_binary h) (exponent_binary h)

theorem indexed_degree_bound (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    (indexed F height z).natDegree ≤ indexedDegreeBound F z :=
  UniformSquarefreeExceptionalBits.degree_le _ _ _ (indexed_degree_eq F hcone height) (indexed_inner_le F height) z

theorem indexed_mass_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    coefficientMass (indexed F height z) ≤ 2 ^ indexedMassBound F z :=
  UniformSquarefreeExceptionalBits.mass_le _ _ _ (indexed_degree_le F height) (indexed_mass_le F height) z

noncomputable def degreeBound (F : Inputs) : List Bool → ℕ :=
  PolynomialFamilyProductBits.budget (count F) (indexedDegreeBound F)

noncomputable def massBound (F : Inputs) : List Bool → ℕ :=
  PolynomialFamilyProductBits.budget (count F) (indexedMassBound F)

theorem degreeBound_binary {F : Inputs} (h : F.Access) : BinaryFn (degreeBound F) :=
  PolynomialFamilyProductBits.budget_binary (FlatAffineFullSourcePositive.count_unary h) (indexedDegreeBound_binary h)

theorem massBound_binary {F : Inputs} (h : F.Access) : BinaryFn (massBound F) :=
  PolynomialFamilyProductBits.budget_binary (FlatAffineFullSourcePositive.count_unary h) (indexedMassBound_binary h)

theorem degree_bound (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    (polynomial F height u).natDegree ≤ degreeBound F u :=
  PolynomialFamilyProductBits.degree_le_budget _ _ _ (indexed_degree_bound F hcone height) u

theorem mass_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    coefficientMass (polynomial F height u) ≤ 2 ^ massBound F u :=
  PolynomialFamilyProductBits.mass_le_budget _ _ _ (indexed_mass_bound F height) u

end LeanCanny.Encoding.FlatAffineHeightExceptional
