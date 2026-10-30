/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointIndexedValues
public import LeanCanny.Algebra.PolynomialBinaryProductSpace

/-! # A native exceptional polynomial for stable endpoint midpoint matching

Stream all midpoint trailing factors and retain the original height
exceptional polynomial. The latter makes every original endpoint height a
root of this refined polynomial. All coefficients and bounds are native.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointExceptional
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def midpoint (F : Inputs) (height : (u : List Bool) → Fin (count F u)) : List Bool → Polynomial ℤ :=
  PolynomialFamilyProductBits.polynomial (FlatAffineEndpointIndexedValues.trailing F height) (FlatAffineEndpointRows.originalCount F)

theorem midpointEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (PrimitivePairBits.coefficient (midpoint F height)) :=
  PolynomialFamilyProductBits.evaluator _ _ (BinaryFn.ofUnary (FlatAffineEndpointRows.originalCount_unary h))
    (FlatAffineEndpointIndexedValues.coefficientEvaluator h height hh)

theorem factor_packet (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool)
    (i : Fin (count F (pairFst r))) :
    FlatAffineEndpointIndexedValues.trailing F height (pair r (BinaryNatCode.encode i.val)) =
      (Geometry.FlatAffineEndpointMidpoint.testPolynomial F height r i).trailingCoeff := by
  simp only [FlatAffineEndpointIndexedValues.trailing, FlatAffineEndpointIndexedValues.polynomial_eq,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem midpoint_ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0) :
    midpoint F height r ≠ 0 := by
  unfold midpoint PolynomialFamilyProductBits.polynomial
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply FlatAffineEndpointIndexedValues.trailing_ne_zero F hcone height _ ?_ a ?_
  · simpa only [pairFst_pair] using hr
  · simpa only [pairFst_pair] using ha

noncomputable def factorMass (F : Inputs) (r : List Bool) : ℕ :=
  FlatAffineEndpointValueBounds.heightBound F r + (FlatAffineEndpointTrailing.innerBound F r + 1).size

theorem factorMass_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) : BinaryFn (factorMass F) :=
  (FlatAffineEndpointValueBounds.heightBound_binary h height (fun r => height (pairFst r))).add
    (((FlatAffineEndpointTrailing.innerBound_binary h height (fun r => height (pairFst r))).add (BinaryFn.const 1)).size)

theorem factor_degree_le (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    (FlatAffineEndpointIndexedValues.trailing F height z).natDegree ≤ FlatAffineEndpointTrailing.innerBound F (pairFst z) :=
  FlatAffineEndpointIndexedValues.parameter_degree_le F height z (FlatAffineEndpointIndexedValues.polynomial F height z).natTrailingDegree

theorem factor_mass_le (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    coefficientMass (FlatAffineEndpointIndexedValues.trailing F height z) ≤ 2 ^ factorMass F (pairFst z) := by
  apply coefficientMass_le_pow_of_degree_coeff _ _ _ (factor_degree_le F height z)
  intro k
  exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide)
    (FlatAffineEndpointIndexedValues.height_le F height z (FlatAffineEndpointIndexedValues.polynomial F height z).natTrailingDegree k))

noncomputable def midpointDegree (F : Inputs) (r : List Bool) : ℕ :=
  FlatAffineEndpointRows.originalCount F r * FlatAffineEndpointTrailing.innerBound F r
noncomputable def midpointMass (F : Inputs) (r : List Bool) : ℕ := FlatAffineEndpointRows.originalCount F r * factorMass F r

theorem midpointDegree_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) : BinaryFn (midpointDegree F) :=
  (BinaryFn.ofUnary (FlatAffineEndpointRows.originalCount_unary h)).mul
    (FlatAffineEndpointTrailing.innerBound_binary h height (fun r => height (pairFst r)))

theorem midpointMass_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) : BinaryFn (midpointMass F) :=
  (BinaryFn.ofUnary (FlatAffineEndpointRows.originalCount_unary h)).mul (factorMass_binary h height)

theorem midpoint_degree_le (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool) :
    (midpoint F height r).natDegree ≤ midpointDegree F r := by
  apply PolynomialFamilyProductBits.degree_le _ _ _ ?_ r
  intro s i
  simpa only [pairFst_pair] using factor_degree_le F height (pair s (BinaryNatCode.encode i))

theorem midpoint_mass_le (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool) :
    coefficientMass (midpoint F height r) ≤ 2 ^ midpointMass F r := by
  apply PolynomialFamilyProductBits.mass_le _ _ _ ?_ r
  intro s i
  simpa only [pairFst_pair] using factor_mass_le F height (pair s (BinaryNatCode.encode i))

noncomputable def polynomial (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool) : Polynomial ℤ :=
  FlatAffineHeightSlabExceptional.polynomial F height (pairFst r) * midpoint F height r

theorem evaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (PrimitivePairBits.coefficient (polynomial F height)) :=
  PolynomialBinaryProductBits.evaluator _ _
    (PolynomialFamilyProductBits.reindexEvaluator (FlatAffineHeightSlabExceptional.evaluator h height hh) pairFst pairFst_mem_FP)
    (midpointEvaluator h height hh)

theorem ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0) :
    polynomial F height r ≠ 0 :=
  mul_ne_zero (FlatAffineHeightSlabExceptional.ne_zero F hcone height (pairFst r)) (midpoint_ne_zero F hcone height r hr a ha)

theorem retains_endpoint {K : Type*} [CommRing K] (phi : Polynomial ℤ →+* K)
    (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool)
    (ha : phi (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0) : phi (polynomial F height r) = 0 := by
  rw [polynomial, map_mul, ha, zero_mul]

theorem avoids {K : Type*} [Field K] (phi : Polynomial ℤ →+* K)
    (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool)
    (ht : phi (polynomial F height r) ≠ 0) (i : Fin (count F (pairFst r))) :
    phi (Geometry.FlatAffineEndpointMidpoint.testPolynomial F height r i).trailingCoeff ≠ 0 := by
  have H := (mul_ne_zero_iff.mp (by simpa only [polynomial, map_mul] using ht)).2
  have Hall : ∀ j < FlatAffineEndpointRows.originalCount F r,
      phi (FlatAffineEndpointIndexedValues.trailing F height (pair r (BinaryNatCode.encode j))) ≠ 0 := by
    simpa only [midpoint, PolynomialFamilyProductBits.polynomial, map_prod, Finset.prod_ne_zero_iff, Finset.mem_range] using H
  have Hi := Hall i.val i.isLt
  rwa [factor_packet F height r i] at Hi

noncomputable def degreeBound (F : Inputs) (r : List Bool) : ℕ :=
  FlatAffineHeightSlabExceptional.degreeBound F (pairFst r) + midpointDegree F r
noncomputable def massBound (F : Inputs) (r : List Bool) : ℕ :=
  FlatAffineHeightSlabExceptional.massBound F (pairFst r) + midpointMass F r

theorem degreeBound_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) : BinaryFn (degreeBound F) :=
  BinaryFn.add ((FlatAffineHeightSlabExceptional.degreeBound_binary h height).comp pairFst_mem_FP) (midpointDegree_binary h height)

theorem massBound_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) : BinaryFn (massBound F) :=
  BinaryFn.add ((FlatAffineHeightSlabExceptional.massBound_binary h height).comp pairFst_mem_FP) (midpointMass_binary h height)

theorem degree_le (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) : (polynomial F height r).natDegree ≤ degreeBound F r :=
  Polynomial.natDegree_mul_le.trans (Nat.add_le_add (FlatAffineHeightSlabExceptional.degree_bound F hcone height (pairFst r))
    (midpoint_degree_le F height r))

theorem mass_le (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool) :
    coefficientMass (polynomial F height r) ≤ 2 ^ massBound F r := by
  apply (coefficientMass_mul_le _ _).trans
  exact (Nat.mul_le_mul (FlatAffineHeightSlabExceptional.mass_bound F height (pairFst r)) (midpoint_mass_le F height r)).trans_eq
    (pow_add _ _ _).symm

end LeanCanny.Encoding.FlatAffineEndpointExceptional
