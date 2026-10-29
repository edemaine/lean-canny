/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineFullSourcePositiveMacaulay
public import LeanCanny.Algebra.SubtractiveCharacteristicSpace
public import LeanCanny.Algebra.PolynomialTrailingCoefficientSpace

/-! # Native coefficients of complete flat coordinate annihilators

The original-source flat rows supply the Macaulay matrix. A native determinant
reader and lowest-coefficient scan compute the actual nonzero coordinate
equation, with binary degree and height bounds and no finiteness oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineFullSourcePositiveCoordinateCoefficient
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR BoundedFullWriter MatrixPower
open FlatAffineFullSourcePositiveMacaulay (layout system)
open FlatAffineFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatAffineFullSourcePositive.system FlatAffineFullSourceTower.degree
  FlatAffineFullSourceTower.mass FlatAffineFullSourcePositiveCoordinate.width
  FlatAffineFullSourcePositiveCoordinate.coefficientBits

noncomputable def matrix (F : Inputs) (coordinate : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (u : List Bool) :=
  MacaulayIntegerPolynomialBits.matrix (layout F) (system F coordinate) u

noncomputable def characteristic (F : Inputs) (coordinate : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (u : List Bool) : Polynomial (Polynomial ℤ) :=
  (AffineCharacteristic.subtractiveMatrix (matrix F coordinate u)).det

theorem matrix_degree (F : Inputs) (coordinate : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (u : List Bool)
    (i j : Fin (FlatAffineFullSourcePositiveCoordinate.matrixCount F u)) :
    (matrix F coordinate u i j).natDegree ≤ 1 :=
  Macaulay.polynomial_entry_degree_le _ _ _ 1
    (AffineCoordinateSystem.coefficient_degree _ _ _) i j

theorem matrix_mass (F : Inputs) (coordinate : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (u : List Bool)
    (i j : Fin (FlatAffineFullSourcePositiveCoordinate.matrixCount F u)) :
    coefficientMass (matrix F coordinate u i j) ≤
      2 ^ (FlatAffineFullSourceTower.mass F u + 2) :=
  Macaulay.matrix_entry_mass_le _ _ _ _
    (AffineCoordinateSystem.coefficient_mass _ _ _ _
      (fun r _ => (MvMass.coeff_le _ _).trans
        (FlatAffineFullSourcePositive.polynomial_mass F u r))) i j

theorem characteristic_degree (F : Inputs) (coordinate : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (u : List Bool) :
    (characteristic F coordinate u).natDegree =
      FlatAffineFullSourcePositiveCoordinate.matrixCount F u := by
  simpa only [characteristic, Fintype.card_fin, layout, FlatAffineFullSourcePositiveCoordinate.matrixCount, Function.comp_apply] using
    AffineCharacteristic.subtractive_det_natDegree (matrix F coordinate u)

theorem characteristic_inner_degree (F : Inputs) (coordinate : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (u : List Bool) (i : ℕ) :
    ((characteristic F coordinate u).coeff i).natDegree ≤
      FlatAffineFullSourcePositiveCoordinate.matrixCount F u := by
  simpa only [characteristic, Fintype.card_fin, Nat.mul_one] using
    CharacteristicLowestBounds.coefficient_degree_le _ 1 (matrix_degree F coordinate u) i

theorem characteristic_coefficient_bits (F : Inputs) (coordinate : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (u : List Bool) (i j : ℕ) :
    (((characteristic F coordinate u).coeff i).coeff j).natAbs.size ≤
      FlatAffineFullSourcePositiveCoordinate.coefficientBits F u := by
  simpa only [characteristic, Fintype.card_fin, FlatAffineFullSourcePositiveCoordinate.coefficientBits, Nat.add_assoc] using
    CharacteristicLowestBounds.all_coefficient_size_le _
      (FlatAffineFullSourceTower.mass F u + 2)
      (matrix_mass F coordinate u) i j

theorem lowest_eq (F : Inputs) (coordinate : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (u : List Bool) :
    (characteristic F coordinate u).trailingCoeff =
      FlatAffineFullSourcePositiveCoordinate.polynomial F u (coordinate u) := by
  unfold characteristic matrix MacaulayIntegerPolynomialBits.matrix FlatAffineFullSourcePositiveCoordinate.polynomial
    AffineCoordinateEliminant.polynomial MacaulayLowestBounds.polynomial CharacteristicLowestBounds.lowest
  rw [FlatAffineFullSourcePositiveMacaulay.degrees_eq]
  rfl

noncomputable def reader {F : Inputs} (h : F.Access)
    (coordinate : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u))
    (hc : UnaryFn (fun u => (coordinate u).val)) :
    CertifiedPolynomial.BivariateReader (characteristic F coordinate) :=
  SubtractiveCharacteristicBits.reader (FlatAffineFullSourcePositiveCoordinate.matrixCount F) (fun _ => 1)
    (matrix F coordinate)
    (fun _ => by unfold FlatAffineFullSourcePositiveCoordinate.matrixCount FixedWidthPolynomial.count; positivity)
    (FlatAffineFullSourcePositiveCoordinate.matrixCount_binary h) (BinaryFn.const 1)
    (matrix_degree F coordinate)
    (MacaulayIntegerPolynomialBits.entry (layout F) (FlatAffineFullSourcePositiveMacaulay.coefficient F coordinate))
    (MacaulayIntegerPolynomialBits.entry_evaluator (FlatAffineFullSourcePositiveMacaulay.layout_binary h)
      (FlatAffineFullSourcePositiveMacaulay.coefficient_evaluator h coordinate hc))
    (MacaulayIntegerPolynomialBits.entry_packet (layout F) (system F coordinate)
      _ (FlatAffineFullSourcePositiveMacaulay.coefficient_packet F coordinate))

noncomputable def value (F : Inputs) (coordinate : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u))
    (q : List Bool) : List Bool :=
  residueBits (((FlatAffineFullSourcePositiveCoordinate.polynomial F (pairFst (pairFst q))
    (coordinate (pairFst (pairFst q)))).coeff (Nat.fromBitsLE (pairSnd q)) : ℤ) :
      ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1))

theorem value_packet (F : Inputs) (coordinate : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u))
    (u m : List Bool) (j : ℕ) :
    value F coordinate (pair (pair u m) (BinaryNatCode.encode j)) =
      residueBits (((FlatAffineFullSourcePositiveCoordinate.polynomial F u (coordinate u)).coeff j : ℤ) :
        ZMod (Nat.fromBitsLE m + 1)) := by
  generalize hz : pair (pair u m) (BinaryNatCode.encode j) = z
  have hu : pairFst (pairFst z) = u := by rw [← hz, pairFst_pair, pairFst_pair]
  have hm : pairSnd (pairFst z) = m := by rw [← hz, pairFst_pair, pairSnd_pair]
  have hj : Nat.fromBitsLE (pairSnd z) = j := by rw [← hz, pairSnd_pair, MacaulayBits.fromBits_encode]
  subst u
  subst m
  subst j
  rfl

theorem evaluator {F : Inputs} (h : F.Access)
    (coordinate : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u))
    (hc : UnaryFn (fun u => (coordinate u).val)) : SpaceFunction (value F coordinate) := by
  have hn := FlatAffineFullSourcePositiveCoordinate.matrixCount_binary h
  have E := PolynomialTrailingCoefficientBits.evaluator _ (reader h coordinate hc)
    hn hn (FlatAffineFullSourcePositiveCoordinate.coefficientBits_binary h)
    (fun u => (characteristic_degree F coordinate u).le)
    (characteristic_inner_degree F coordinate)
    (characteristic_coefficient_bits F coordinate)
  exact E.congr (funext fun q => by
    unfold PolynomialTrailingCoefficientBits.value value
    rw [lowest_eq])

end LeanCanny.Encoding.FlatAffineFullSourcePositiveCoordinateCoefficient
