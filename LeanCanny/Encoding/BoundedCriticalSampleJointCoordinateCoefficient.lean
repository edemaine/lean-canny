/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleJointMacaulay
public import LeanCanny.Algebra.SubtractiveCharacteristicSpace
public import LeanCanny.Algebra.PolynomialTrailingCoefficientSpace

/-! # Native coefficients of regular child coordinate annihilators

The implicit joint rows supply the Macaulay matrix. A native determinant
reader and lowest-coefficient scan compute the actual nonzero coordinate
equation, with binary degree and height bounds and no finiteness oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleJointCoordinateCoefficient
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR BoundedFullWriter MatrixPower
open BoundedCriticalSampleJointMacaulay (layout system)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleJointSource.system BoundedCriticalSampleJointSource.degree
  BoundedCriticalSampleJointSource.massExponent BoundedCriticalSampleJointCoordinate.width
  BoundedCriticalSampleJointCoordinate.coefficientBits

noncomputable def matrix (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (u : List Bool) :=
  MacaulayIntegerPolynomialBits.matrix (layout P read k) (system P read o k w bits pivot coordinate) u

noncomputable def characteristic (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (u : List Bool) : Polynomial (Polynomial ℤ) :=
  (AffineCharacteristic.subtractiveMatrix (matrix P read o k w bits pivot coordinate u)).det

theorem matrix_degree (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (u : List Bool)
    (i j : Fin (BoundedCriticalSampleJointCoordinate.count P read k u)) :
    (matrix P read o k w bits pivot coordinate u i j).natDegree ≤ 1 :=
  Macaulay.polynomial_entry_degree_le _ _ _ 1
    (AffineCoordinateSystem.coefficient_degree _ _ _) i j

theorem matrix_mass (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (u : List Bool)
    (i j : Fin (BoundedCriticalSampleJointCoordinate.count P read k u)) :
    coefficientMass (matrix P read o k w bits pivot coordinate u i j) ≤
      2 ^ (BoundedCriticalSampleJointSource.massExponent P read k w u + 2) :=
  Macaulay.matrix_entry_mass_le _ _ _ _
    (AffineCoordinateSystem.coefficient_mass _ _ _ _
      (fun r _ => (MvMass.coeff_le _ _).trans
        (BoundedCriticalSampleJointSource.polynomial_mass P read o k w bits u (pivot u) r))) i j

theorem characteristic_degree (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (u : List Bool) :
    (characteristic P read o k w bits pivot coordinate u).natDegree =
      BoundedCriticalSampleJointCoordinate.count P read k u := by
  simpa only [characteristic, Fintype.card_fin, layout, BoundedCriticalSampleJointCoordinate.count] using
    AffineCharacteristic.subtractive_det_natDegree (matrix P read o k w bits pivot coordinate u)

theorem characteristic_inner_degree (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (u : List Bool) (i : ℕ) :
    ((characteristic P read o k w bits pivot coordinate u).coeff i).natDegree ≤
      BoundedCriticalSampleJointCoordinate.count P read k u := by
  simpa only [characteristic, Fintype.card_fin, Nat.mul_one] using
    CharacteristicLowestBounds.coefficient_degree_le _ 1 (matrix_degree P read o k w bits pivot coordinate u) i

theorem characteristic_coefficient_bits (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (u : List Bool) (i j : ℕ) :
    (((characteristic P read o k w bits pivot coordinate u).coeff i).coeff j).natAbs.size ≤
      BoundedCriticalSampleJointCoordinate.coefficientBits P read k w u := by
  simpa only [characteristic, Fintype.card_fin, BoundedCriticalSampleJointCoordinate.coefficientBits, Nat.add_assoc] using
    CharacteristicLowestBounds.all_coefficient_size_le _
      (BoundedCriticalSampleJointSource.massExponent P read k w u + 2)
      (matrix_mass P read o k w bits pivot coordinate u) i j

theorem lowest_eq (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (u : List Bool) :
    (characteristic P read o k w bits pivot coordinate u).trailingCoeff =
      BoundedCriticalSampleJointCoordinate.polynomial P read o k w bits u (pivot u) (coordinate u) := by
  unfold characteristic matrix MacaulayIntegerPolynomialBits.matrix BoundedCriticalSampleJointCoordinate.polynomial
    AffineCoordinateEliminant.polynomial MacaulayLowestBounds.polynomial CharacteristicLowestBounds.lowest
  rw [BoundedCriticalSampleJointMacaulay.degrees_eq]
  rfl

noncomputable def reader {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {o k w : List Bool → ℕ} (ho : BinaryFn o) (hk : UnaryFn k) (hw : UnaryFn w)
    {bits : List Bool → List Bool} (hbits : bits ∈ FP)
    (pivot : (u : List Bool) → Fin (k u)) (hp : BinaryFn (fun u => (pivot u).val))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (hc : UnaryFn (fun u => (coordinate u).val))
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    CertifiedPolynomial.BivariateReader (characteristic P read o k w bits pivot coordinate) :=
  SubtractiveCharacteristicBits.reader (BoundedCriticalSampleJointCoordinate.count P read k) (fun _ => 1)
    (matrix P read o k w bits pivot coordinate)
    (fun _ => by unfold BoundedCriticalSampleJointCoordinate.count FixedWidthPolynomial.count; positivity)
    (BoundedCriticalSampleJointCoordinate.count_binary h read hr hk) (BinaryFn.const 1)
    (matrix_degree P read o k w bits pivot coordinate)
    (MacaulayIntegerPolynomialBits.entry (layout P read k)
      (BoundedCriticalSampleJointMacaulay.coefficient P read o k w bits pivot coordinate))
    (MacaulayIntegerPolynomialBits.entry_evaluator (BoundedCriticalSampleJointMacaulay.layout_binary h read hr hk)
      (BoundedCriticalSampleJointMacaulay.coefficient_evaluator h read hr ho hk hw hbits pivot hp coordinate hc ha))
    (MacaulayIntegerPolynomialBits.entry_packet (layout P read k) (system P read o k w bits pivot coordinate)
      _ (BoundedCriticalSampleJointMacaulay.coefficient_packet P read o k w bits pivot coordinate))

noncomputable def value (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (q : List Bool) : List Bool :=
  residueBits (((BoundedCriticalSampleJointCoordinate.polynomial P read o k w bits (pairFst (pairFst q))
    (pivot (pairFst (pairFst q))) (coordinate (pairFst (pairFst q)))).coeff (Nat.fromBitsLE (pairSnd q)) : ℤ) :
      ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1))

theorem value_packet (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (u m : List Bool) (j : ℕ) :
    value P read o k w bits pivot coordinate (pair (pair u m) (BinaryNatCode.encode j)) =
      residueBits (((BoundedCriticalSampleJointCoordinate.polynomial P read o k w bits u (pivot u) (coordinate u)).coeff j : ℤ) :
        ZMod (Nat.fromBitsLE m + 1)) := by
  generalize hz : pair (pair u m) (BinaryNatCode.encode j) = z
  have hu : pairFst (pairFst z) = u := by rw [← hz, pairFst_pair, pairFst_pair]
  have hm : pairSnd (pairFst z) = m := by rw [← hz, pairFst_pair, pairSnd_pair]
  have hj : Nat.fromBitsLE (pairSnd z) = j := by rw [← hz, pairSnd_pair, MacaulayBits.fromBits_encode]
  subst u
  subst m
  subst j
  rfl

theorem evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {o k w : List Bool → ℕ} (ho : BinaryFn o) (hk : UnaryFn k) (hw : UnaryFn w)
    {bits : List Bool → List Bool} (hbits : bits ∈ FP)
    (pivot : (u : List Bool) → Fin (k u)) (hp : BinaryFn (fun u => (pivot u).val))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (hc : UnaryFn (fun u => (coordinate u).val))
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (value P read o k w bits pivot coordinate) := by
  have hn := BoundedCriticalSampleJointCoordinate.count_binary h read hr hk
  have E := PolynomialTrailingCoefficientBits.evaluator _ (reader h read hr ho hk hw hbits pivot hp coordinate hc ha)
    hn hn (BoundedCriticalSampleJointCoordinate.coefficientBits_binary h read hr hk hw)
    (fun u => (characteristic_degree P read o k w bits pivot coordinate u).le)
    (characteristic_inner_degree P read o k w bits pivot coordinate)
    (characteristic_coefficient_bits P read o k w bits pivot coordinate)
  exact E.congr (funext fun q => by
    unfold PolynomialTrailingCoefficientBits.value value
    rw [lowest_eq])

end LeanCanny.Encoding.BoundedCriticalSampleJointCoordinateCoefficient
