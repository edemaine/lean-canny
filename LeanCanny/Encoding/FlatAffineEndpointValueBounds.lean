/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointValues
public import LeanCanny.Algebra.FrozenAffineMass

/-! # Source-derived height budgets for frozen endpoint midpoint values

The retained polynomial and original tower bound every extended row. Those
bounds pass through both Gram stages. The midpoint test has mass at most four.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointValueBounds
open LeanCanny.Algebra LeanCanny.Computation MatrixPower MvPolynomial
open FlatAffineFullSourceTower (Inputs mass)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def integerExponent (F : Inputs) (r : List Bool) : ℕ :=
  mass F (pairFst r) + FlatAffineHeightSlabExceptional.massBound F (pairFst r) + 1
noncomputable def sourceExponent (F : Inputs) (r : List Bool) : ℕ := integerExponent F r + 1
noncomputable def coordinateExponent (F : Inputs) (r : List Bool) : ℕ :=
  ProjectiveValueGram.massExponent (FlatAffineEndpointRows.arity F r)
    (AffineRingCoordinates.width (FlatAffineEndpointPreparation.degrees F r)) (sourceExponent F r)
noncomputable def gridExponent (F : Inputs) (r : List Bool) : ℕ := coordinateExponent F r + 2
noncomputable def heightBound (F : Inputs) (r : List Bool) : ℕ :=
  ProjectiveValueGram.massExponent (FlatAffineEndpointRows.arity F r) (FlatAffineEndpointValues.width F r) (gridExponent F r) + 1

theorem integerExponent_binary {F : Inputs} (h : F.Access)
    (height : (u : List Bool) → Fin (count F u)) : BinaryFn (integerExponent F) := by
  have hp : BinaryFn (fun r => mass F (pairFst r)) := (FlatAffineFullSourceTower.mass_binary h).comp pairFst_mem_FP
  have he : BinaryFn (fun r => FlatAffineHeightSlabExceptional.massBound F (pairFst r)) :=
    (FlatAffineHeightSlabExceptional.massBound_binary h height).comp pairFst_mem_FP
  exact (hp.add he).add (BinaryFn.const 1)

theorem sourceExponent_binary {F : Inputs} (h : F.Access)
    (height : (u : List Bool) → Fin (count F u)) : BinaryFn (sourceExponent F) :=
  (integerExponent_binary h height).add (BinaryFn.const 1)

theorem coordinateExponent_binary {F : Inputs} (h : F.Access)
    (height : (u : List Bool) → Fin (count F u)) : BinaryFn (coordinateExponent F) := by
  have hn := (FlatAffineEndpointGram.family F height (FlatAffineEndpointRows.zero F)).parameter.affine.homogeneous.dimension_binary
    (FlatAffineEndpointGram.controls h height (FlatAffineEndpointRows.zero F))
  have hb := sourceExponent_binary h height
  exact (hn.size.mul hn).add (hn.mul (hn.size.add ((BinaryFn.const 2).mul (hb.add (BinaryFn.const 1)))))

theorem gridExponent_binary {F : Inputs} (h : F.Access)
    (height : (u : List Bool) → Fin (count F u)) : BinaryFn (gridExponent F) :=
  (coordinateExponent_binary h height).add (BinaryFn.const 2)

theorem heightBound_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) : BinaryFn (heightBound F) := by
  have hn := FlatAffineEndpointValues.valueDimension_binary h height index
  have hb := gridExponent_binary h height
  exact ((hn.size.mul hn).add (hn.mul (hn.size.add ((BinaryFn.const 2).mul (hb.add (BinaryFn.const 1)))))).add (BinaryFn.const 1)

theorem integer_mass_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool)
    (i : Fin (FlatAffineEndpointRows.arity F r)) :
    MvMass.mass (FlatAffineEndpointPreparation.system F height r i) ≤ 2 ^ integerExponent F r :=
  FrozenAffineCopies.system_mass _ _ _ _ _ _ (FlatAffinePowerPositive.polynomial_mass F (pairFst r))
    (FlatAffineHeightSlabExceptional.mass_bound F height (pairFst r)) i

theorem source_mass_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool)
    (i : Fin (FlatAffineEndpointRows.arity F r)) (e : Fin (FlatAffineEndpointRows.arity F r) →₀ ℕ) :
    coefficientMass ((AffineConstantParameterShift.system (FlatAffineEndpointPreparation.system F height r)
      (fun j => if j = FlatAffineEndpointGram.active F height r then Polynomial.X else 0) i).coeff e) ≤ 2 ^ sourceExponent F r := by
  rw [AffineConstantParameterShift.coefficient]
  apply (coefficientMass_sub_le _ _).trans
  have hp : coefficientMass (Polynomial.C ((FlatAffineEndpointPreparation.system F height r i).coeff e)) ≤ 2 ^ integerExponent F r := by
    rw [coefficientMass_C]
    exact (MvMass.coeff_le _ _).trans (integer_mass_bound F height r i)
  have hs : coefficientMass (if e = 0 then (if i = FlatAffineEndpointGram.active F height r then Polynomial.X else 0) else 0) ≤ 1 := by
    split_ifs <;> first | simp | simpa only [pow_one] using (coefficientMass_X_pow 1).le
  apply (Nat.add_le_add hp hs).trans
  change 2 ^ integerExponent F r + 1 ≤ 2 ^ (integerExponent F r + 1)
  rw [pow_succ]
  have H := Nat.one_le_pow (integerExponent F r) 2 (by decide)
  omega

theorem coordinate_mass_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool)
    (i : Fin (FlatAffineEndpointRows.arity F r)) :
    NestedMass.mass (FlatAffineEndpointGrid.coordinate F height r i) ≤ 2 ^ coordinateExponent F r := by
  change NestedMass.mass (AffineRingGramEliminant.annihilator
    (AffineRingCoordinates.homogeneousRows (AffineConstantParameterShift.system (FlatAffineEndpointPreparation.system F height r)
      (fun j => if j = FlatAffineEndpointGram.active F height r then Polynomial.X else 0)) (FlatAffineEndpointPreparation.degrees F r))
    (FlatAffineEndpointPreparation.degrees F r) (AffineRingCoordinates.width (FlatAffineEndpointPreparation.degrees F r)) i.succ) ≤ _
  rw [← AffineParameterCoordinateBits.coordinate_value_eq]
  apply ProjectiveValueGram.annihilator_mass_le_two_pow
  · intro j e
    exact AffineValueGramBits.homogenized_mass_bound _ _ _ (source_mass_bound F height r j) e
  · intro e
    simp only [coeff_X]
    split_ifs
    · change coefficientMass (Polynomial.C (1 : ℤ)) ≤ 2 ^ sourceExponent F r
      rw [coefficientMass_C]
      exact Nat.one_le_pow _ _ (by decide)
    · simp

theorem original_mass_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) (r : List Bool)
    (i : Fin (FlatAffineEndpointRows.arity F r + 1)) (e : Fin (FlatAffineEndpointRows.arity F r) →₀ ℕ) :
    coefficientMass (((FlatAffineEndpointValues.family F height index).affine.original r i).coeff e) ≤ 2 ^ gridExponent F r := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change coefficientMass (Polynomial.C ((FrozenAffineCopies.midpoint (index r)).coeff e)) ≤ _
    rw [coefficientMass_C]
    apply ((MvMass.coeff_le _ _).trans (FrozenAffineCopies.midpoint_mass _)).trans
    change 2 ^ 2 ≤ 2 ^ (coordinateExponent F r + 2)
    exact Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)
  · change coefficientMass (((FlatAffineEndpointGrid.coordinate F height r j).toMvPolynomial j).coeff e) ≤ _
    rw [DiagonalParameterBits.coefficient]
    split_ifs
    · exact ((NestedMass.coeff_le _ _).trans (coordinate_mass_bound F height r j)).trans
        (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
    · simp

theorem height_le (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) (r : List Bool) (j k : ℕ) :
    (((((FlatAffineEndpointValues.family F height index).affine.homogeneous.annihilator r).coeff j).coeff k).natAbs).size ≤
      heightBound F r :=
  (FlatAffineEndpointValues.family F height index).affine.height_le (gridExponent F) (original_mass_bound F height index) r j k

end LeanCanny.Encoding.FlatAffineEndpointValueBounds
