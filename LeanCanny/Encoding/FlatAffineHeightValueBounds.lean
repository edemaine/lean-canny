/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineHeightValues
public import LeanCanny.Algebra.AffineValueGramHeight

/-! # Native coefficient-height budgets for actual affine-height values

The original source mass bounds the parameter-shifted rows. The first Gram
mass bound controls every coordinate coefficient; the second controls the
equation-value certificate. Only their binary exponents are computed.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineHeightValueBounds
open LeanCanny.Algebra LeanCanny.Computation MatrixPower MvPolynomial
open FlatAffineFullSourceTower (Inputs mass)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def sourceExponent (F : Inputs) (u : List Bool) := mass F u + 1
noncomputable def coordinateExponent (F : Inputs) (u : List Bool) :=
  ProjectiveValueGram.massExponent (count F u) (FlatAffinePowerControls.width F u) (sourceExponent F u)
noncomputable def gridExponent (F : Inputs) (u : List Bool) := coordinateExponent F u + sourceExponent F u
noncomputable def heightBound (F : Inputs) (row : (u : List Bool) → Fin (count F u)) (u : List Bool) :=
  ProjectiveValueGram.massExponent (count F u) (FlatAffineHeightValues.width F row u) (gridExponent F u) + 1

theorem sourceExponent_binary {F : Inputs} (h : F.Access) : BinaryFn (sourceExponent F) :=
  (FlatAffineFullSourceTower.mass_binary h).add (BinaryFn.const 1)

theorem coordinateExponent_binary {F : Inputs} (h : F.Access) : BinaryFn (coordinateExponent F) := by
  have hn := FlatAffinePowerGramLayout.dimension_binary h
  have hb := sourceExponent_binary h
  exact (hn.size.mul hn).add (hn.mul (hn.size.add ((BinaryFn.const 2).mul (hb.add (BinaryFn.const 1)))))

theorem gridExponent_binary {F : Inputs} (h : F.Access) : BinaryFn (gridExponent F) :=
  (coordinateExponent_binary h).add (sourceExponent_binary h)

theorem heightBound_binary {F : Inputs} (h : F.Access) (height row : (u : List Bool) → Fin (count F u))
    (hr : UnaryFn (fun u => (row u).val)) : BinaryFn (heightBound F row) := by
  have hn := FlatAffineHeightValues.valueDimension_binary h height row hr
  have hb := gridExponent_binary h
  exact ((hn.size.mul hn).add (hn.mul (hn.size.add ((BinaryFn.const 2).mul (hb.add (BinaryFn.const 1)))))).add (BinaryFn.const 1)

lemma source_mass_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (u : List Bool)
    (i : Fin (count F u)) (e : Fin (count F u) →₀ ℕ) :
    coefficientMass ((AffineConstantParameterShift.system (FlatAffinePowerPositive.system F u)
      (fun j => if j = height u then Polynomial.X else 0) i).coeff e) ≤ 2 ^ sourceExponent F u := by
  have hp := (MvMass.coeff_le (FlatAffinePowerPositive.system F u i) e).trans
    (FlatAffinePowerPositive.polynomial_mass F u i)
  have hx : coefficientMass (Polynomial.X : Polynomial ℤ) = 1 := by
    simpa only [pow_one] using coefficientMass_X_pow 1
  have hs : coefficientMass (if e = 0 then (if i = height u then (Polynomial.X : Polynomial ℤ) else 0) else 0) ≤ 1 := by
    by_cases he : e = 0
    · rw [ite_eq_left he]
      by_cases hi : i = height u
      · rw [ite_eq_left hi, hx]
      · simp [hi]
    · simp [he]
  rw [AffineConstantParameterShift.coefficient]
  apply (coefficientMass_sub_le _ _).trans
  have hl : coefficientMass (Polynomial.C ((FlatAffinePowerPositive.system F u i).coeff e)) ≤ 2 ^ mass F u := by
    simpa only [coefficientMass_C] using hp
  apply (Nat.add_le_add hl hs).trans
  change 2 ^ mass F u + 1 ≤ 2 ^ (mass F u + 1)
  rw [pow_succ]
  have hh : 1 ≤ 2 ^ mass F u := Nat.one_le_pow _ _ (by decide)
  omega

lemma coordinate_mass_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (u : List Bool)
    (i : Fin (count F u)) : NestedMass.mass (FlatAffineHeightGrid.coordinate F height u i) ≤ 2 ^ coordinateExponent F u := by
  change NestedMass.mass (AffineRingGramEliminant.annihilator
    (AffineRingCoordinates.homogeneousRows (AffineConstantParameterShift.system (FlatAffinePowerPositive.system F u)
      (fun j => if j = height u then Polynomial.X else 0)) (FlatAffinePowerPositive.degree F u))
    (FlatAffinePowerPositive.degree F u) (AffineRingCoordinates.width (FlatAffinePowerPositive.degree F u)) i.succ) ≤ _
  rw [show AffineRingCoordinates.width (FlatAffinePowerPositive.degree F u) = FlatAffinePowerControls.width F u from
    (FlatAffinePowerGramLayout.width_eq F u).symm]
  rw [← AffineParameterCoordinateBits.coordinate_value_eq]
  apply ProjectiveValueGram.annihilator_mass_le_two_pow
  · intro j e
    exact AffineValueGramBits.homogenized_mass_bound _ _ _ (source_mass_bound F height u j) e
  · intro e
    simp only [coeff_X]
    split_ifs
    · change coefficientMass (Polynomial.C (1 : ℤ)) ≤ 2 ^ sourceExponent F u
      rw [coefficientMass_C]
      exact Nat.one_le_pow _ _ (by decide)
    · simp

lemma original_mass_bound (F : Inputs) (height row : (u : List Bool) → Fin (count F u))
    (u : List Bool) (i : Fin (count F u + 1)) (e : Fin (count F u) →₀ ℕ) :
    coefficientMass (((FlatAffineHeightValues.family F height row).affine.original u i).coeff e) ≤ 2 ^ gridExponent F u := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (source_mass_bound F height u (row u) e).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  · change coefficientMass (((FlatAffineHeightGrid.coordinate F height u j).toMvPolynomial j).coeff e) ≤ _
    rw [DiagonalParameterBits.coefficient]
    split_ifs
    · exact ((NestedMass.coeff_le _ _).trans (coordinate_mass_bound F height u j)).trans
        (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
    · simp

theorem height_le (F : Inputs) (height row : (u : List Bool) → Fin (count F u)) (u : List Bool) (j k : ℕ) :
    (((((FlatAffineHeightValues.family F height row).affine.homogeneous.annihilator u).coeff j).coeff k).natAbs).size ≤
      heightBound F row u :=
  (FlatAffineHeightValues.family F height row).affine.height_le (gridExponent F) (original_mass_bound F height row) u j k

end LeanCanny.Encoding.FlatAffineHeightValueBounds
