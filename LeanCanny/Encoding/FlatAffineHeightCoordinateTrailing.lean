/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineHeightExceptional
public import LeanCanny.Encoding.FlatAffineHeightTrailing

/-! # Native zero-test exceptional factors for actual height coordinates

Lowest nonzero coordinate coefficients control zeros of spatial coordinates
and critical multipliers along retained curves. The indexed coefficient scan
and its bounds come from the original varying-height grid reader.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineHeightCoordinateTrailing
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def heightBound (F : Inputs) (z : List Bool) : ℕ := FlatAffineHeightExceptional.exponent F z + 1
theorem heightBound_binary {F : Inputs} (h : F.Access) : BinaryFn (heightBound F) :=
  (FlatAffineHeightExceptional.exponent_binary h).add (BinaryFn.const 1)

theorem coefficient_height (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) (i j : ℕ) :
    (((FlatAffineHeightGrid.indexed F height z).coeff i).coeff j).natAbs.size ≤ heightBound F z := by
  have H := Nat.size_le_size ((coeff_natAbs_le_coefficientMass _ j).trans
    (FlatAffineHeightExceptional.indexed_mass_le F height z i))
  simpa only [heightBound, Nat.size_pow] using H

noncomputable def indexed (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) : Polynomial ℤ :=
  (FlatAffineHeightGrid.indexed F height z).trailingCoeff

theorem indexedEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (PrimitivePairBits.coefficient (indexed F height)) := by
  have E := PolynomialTrailingCoefficientBits.evaluator _ (FlatAffineHeightGrid.indexedReader h height hh)
    (FlatAffineHeightExceptional.degree_binary h) (FlatAffineHeightExceptional.degree_binary h) (heightBound_binary h)
    (FlatAffineHeightExceptional.indexed_degree_le F height) (FlatAffineHeightExceptional.indexed_inner_le F height)
    (coefficient_height F height)
  exact (E.precompose FlatAffineHeightTrailing.primitiveQuery FlatAffineHeightTrailing.primitiveQuery_FP).congr
    (funext fun q => by
      let read (c k m : List Bool) := residueBits (((indexed F height c).coeff
        (Nat.fromBitsLE k) : ℤ) : ZMod (Nat.fromBitsLE m + 1))
      change read (pairFst (pairFst (FlatAffineHeightTrailing.primitiveQuery q)))
          (pairSnd (FlatAffineHeightTrailing.primitiveQuery q))
          (pairSnd (pairFst (FlatAffineHeightTrailing.primitiveQuery q))) =
        read (pairFst (pairFst q)) (pairSnd (pairFst q)) (pairSnd q)
      simp only [FlatAffineHeightTrailing.primitiveQuery, pairFst_pair, pairSnd_pair])

theorem indexed_ne_zero (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (z : List Bool) : indexed F height z ≠ 0 := by
  apply Polynomial.trailingCoeff_ne_zero.mpr
  apply Polynomial.ne_zero_of_natDegree_gt
  rw [FlatAffineHeightExceptional.indexed_degree_eq F cone height]
  exact Nat.zero_lt_succ _

theorem indexed_degree_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    (indexed F height z).natDegree ≤ FlatAffineHeightExceptional.degree F z :=
  FlatAffineHeightExceptional.indexed_inner_le F height z _
theorem indexed_mass_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    coefficientMass (indexed F height z) ≤ 2 ^ FlatAffineHeightExceptional.exponent F z :=
  FlatAffineHeightExceptional.indexed_mass_le F height z _

noncomputable def polynomial (F : Inputs) (height : (u : List Bool) → Fin (count F u)) : List Bool → Polynomial ℤ :=
  PolynomialFamilyProductBits.polynomial (indexed F height) (count F)
theorem evaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (PrimitivePairBits.coefficient (polynomial F height)) :=
  PolynomialFamilyProductBits.evaluator _ _ (BinaryFn.ofUnary (FlatAffineFullSourcePositive.count_unary h))
    (indexedEvaluator h height hh)
theorem ne_zero (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) : polynomial F height u ≠ 0 :=
  PolynomialFamilyProductBits.ne_zero _ _ (indexed_ne_zero F cone height) u

theorem avoids {K : Type*} [Field K] (phi : Polynomial ℤ →+* K)
    (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (u : List Bool)
    (ht : phi (polynomial F height u) ≠ 0) (i : Fin (count F u)) :
    phi (FlatAffineHeightGrid.coordinate F height u i).trailingCoeff ≠ 0 := by
  have H : ∀ j < count F u, phi (indexed F height (pair u (BinaryNatCode.encode j))) ≠ 0 := by
    simpa only [polynomial, PolynomialFamilyProductBits.polynomial, map_prod, Finset.prod_ne_zero_iff, Finset.mem_range] using ht
  have HI := H i.val i.isLt
  simpa only [indexed, FlatAffineHeightExceptional.indexed_coordinate_eq] using HI

noncomputable def degreeBound (F : Inputs) : List Bool → ℕ :=
  PolynomialFamilyProductBits.budget (count F) (FlatAffineHeightExceptional.degree F)
noncomputable def massBound (F : Inputs) : List Bool → ℕ :=
  PolynomialFamilyProductBits.budget (count F) (FlatAffineHeightExceptional.exponent F)
theorem degreeBound_binary {F : Inputs} (h : F.Access) : BinaryFn (degreeBound F) :=
  PolynomialFamilyProductBits.budget_binary (FlatAffineFullSourcePositive.count_unary h) (FlatAffineHeightExceptional.degree_binary h)
theorem massBound_binary {F : Inputs} (h : F.Access) : BinaryFn (massBound F) :=
  PolynomialFamilyProductBits.budget_binary (FlatAffineFullSourcePositive.count_unary h) (FlatAffineHeightExceptional.exponent_binary h)
theorem degree_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    (polynomial F height u).natDegree ≤ degreeBound F u :=
  PolynomialFamilyProductBits.degree_le_budget _ _ _ (indexed_degree_bound F height) u
theorem mass_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    coefficientMass (polynomial F height u) ≤ 2 ^ massBound F u :=
  PolynomialFamilyProductBits.mass_le_budget _ _ _ (indexed_mass_bound F height) u

end LeanCanny.Encoding.FlatAffineHeightCoordinateTrailing
