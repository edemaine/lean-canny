/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleJointMacaulay
public import LeanCanny.Algebra.SubtractiveCharacteristicSpace
public import LeanCanny.Algebra.PolynomialTrailingCoefficientSpace

/-! # Native coefficients of regular child coordinate annihilators

The implicit joint rows supply the Macaulay matrix. A native determinant
reader and lowest-coefficient scan compute the actual nonzero coordinate
equation, with binary degree and height bounds and no finiteness oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleJointCoordinateCoefficient
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR BoundedFullWriter MatrixPower
open BoundedFullSampleJointMacaulay (layout system)
open BoundedFullSampleBlock
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleJointSource.system BoundedFullSampleJointSource.degree
  BoundedFullSampleJointSource.massExponent BoundedFullSampleJointCoordinate.width
  BoundedFullSampleJointCoordinate.coefficientBits

noncomputable def matrix (F : Inputs) (w : List Bool → ℕ)
    (bits pull : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.dim u))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (u : List Bool) :=
  MacaulayIntegerPolynomialBits.matrix (layout F pull) (system F w bits pull pivot coordinate) u

noncomputable def characteristic (F : Inputs) (w : List Bool → ℕ)
    (bits pull : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.dim u))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (u : List Bool) : Polynomial (Polynomial ℤ) :=
  (AffineCharacteristic.subtractiveMatrix (matrix F w bits pull pivot coordinate u)).det

theorem matrix_degree (F : Inputs) (w : List Bool → ℕ)
    (bits pull : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.dim u))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (u : List Bool)
    (i j : Fin (BoundedFullSampleJointCoordinate.count F (pull u))) :
    (matrix F w bits pull pivot coordinate u i j).natDegree ≤ 1 :=
  Macaulay.polynomial_entry_degree_le _ _ _ 1
    (AffineCoordinateSystem.coefficient_degree _ _ _) i j

theorem matrix_mass (F : Inputs) (w : List Bool → ℕ)
    (bits pull : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.dim u))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (u : List Bool)
    (i j : Fin (BoundedFullSampleJointCoordinate.count F (pull u))) :
    coefficientMass (matrix F w bits pull pivot coordinate u i j) ≤
      2 ^ (BoundedFullSampleJointSource.massExponent F w (pull u) + 2) :=
  Macaulay.matrix_entry_mass_le _ _ _ _
    (AffineCoordinateSystem.coefficient_mass _ _ _ _
      (fun r _ => (MvMass.coeff_le _ _).trans
        (BoundedFullSampleJointSource.polynomial_mass F w bits (pull u) (pivot (pull u)) r))) i j

theorem characteristic_degree (F : Inputs) (w : List Bool → ℕ)
    (bits pull : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.dim u))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (u : List Bool) :
    (characteristic F w bits pull pivot coordinate u).natDegree =
      BoundedFullSampleJointCoordinate.count F (pull u) := by
  simpa only [characteristic, Fintype.card_fin, layout, BoundedFullSampleJointCoordinate.count, Function.comp_apply] using
    AffineCharacteristic.subtractive_det_natDegree (matrix F w bits pull pivot coordinate u)

theorem characteristic_inner_degree (F : Inputs) (w : List Bool → ℕ)
    (bits pull : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.dim u))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (u : List Bool) (i : ℕ) :
    ((characteristic F w bits pull pivot coordinate u).coeff i).natDegree ≤
      BoundedFullSampleJointCoordinate.count F (pull u) := by
  simpa only [characteristic, Fintype.card_fin, Nat.mul_one] using
    CharacteristicLowestBounds.coefficient_degree_le _ 1 (matrix_degree F w bits pull pivot coordinate u) i

theorem characteristic_coefficient_bits (F : Inputs) (w : List Bool → ℕ)
    (bits pull : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.dim u))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (u : List Bool) (i j : ℕ) :
    (((characteristic F w bits pull pivot coordinate u).coeff i).coeff j).natAbs.size ≤
      BoundedFullSampleJointCoordinate.coefficientBits F w (pull u) := by
  simpa only [characteristic, Fintype.card_fin, BoundedFullSampleJointCoordinate.coefficientBits, Nat.add_assoc] using
    CharacteristicLowestBounds.all_coefficient_size_le _
      (BoundedFullSampleJointSource.massExponent F w (pull u) + 2)
      (matrix_mass F w bits pull pivot coordinate u) i j

theorem lowest_eq (F : Inputs) (w : List Bool → ℕ)
    (bits pull : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.dim u))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (u : List Bool) :
    (characteristic F w bits pull pivot coordinate u).trailingCoeff =
      BoundedFullSampleJointCoordinate.polynomial F w bits (pull u) (pivot (pull u)) (coordinate u) := by
  unfold characteristic matrix MacaulayIntegerPolynomialBits.matrix BoundedFullSampleJointCoordinate.polynomial
    AffineCoordinateEliminant.polynomial MacaulayLowestBounds.polynomial CharacteristicLowestBounds.lowest
  rw [BoundedFullSampleJointMacaulay.degrees_eq]
  rfl

noncomputable def reader {F : Inputs} (h : F.PolyTime)
    {w : List Bool → ℕ} (hw : UnaryFn w)
    {bits pull : List Bool → List Bool} (EB : SpaceFunction bits) (hpull : pull ∈ FP)
    (pivot : (u : List Bool) → Fin (F.dim u)) (hp : BinaryFn (fun u => (pivot u).val))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (hc : UnaryFn (fun u => (coordinate u).val))
    (htP : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c)
    (htS : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u) :
    CertifiedPolynomial.BivariateReader (characteristic F w bits pull pivot coordinate) :=
  SubtractiveCharacteristicBits.reader (BoundedFullSampleJointCoordinate.count F ∘ pull) (fun _ => 1)
    (matrix F w bits pull pivot coordinate)
    (fun _ => by simp only [Function.comp_apply]; unfold BoundedFullSampleJointCoordinate.count FixedWidthPolynomial.count; positivity)
    ((BoundedFullSampleJointCoordinate.count_binary h).comp hpull) (BinaryFn.const 1)
    (matrix_degree F w bits pull pivot coordinate)
    (MacaulayIntegerPolynomialBits.entry (layout F pull)
      (BoundedFullSampleJointMacaulay.coefficient F w bits pull pivot coordinate))
    (MacaulayIntegerPolynomialBits.entry_evaluator (BoundedFullSampleJointMacaulay.layout_binary h hpull)
      (BoundedFullSampleJointMacaulay.coefficient_evaluator h hw EB hpull pivot hp coordinate hc htP htS))
    (MacaulayIntegerPolynomialBits.entry_packet (layout F pull) (system F w bits pull pivot coordinate)
      _ (BoundedFullSampleJointMacaulay.coefficient_packet F w bits pull pivot coordinate))

noncomputable def value (F : Inputs) (w : List Bool → ℕ)
    (bits pull : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.dim u))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (q : List Bool) : List Bool :=
  residueBits (((BoundedFullSampleJointCoordinate.polynomial F w bits (pull (pairFst (pairFst q)))
    (pivot (pull (pairFst (pairFst q)))) (coordinate (pairFst (pairFst q)))).coeff (Nat.fromBitsLE (pairSnd q)) : ℤ) :
      ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1))

theorem value_packet (F : Inputs) (w : List Bool → ℕ)
    (bits pull : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.dim u))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (u m : List Bool) (j : ℕ) :
    value F w bits pull pivot coordinate (pair (pair u m) (BinaryNatCode.encode j)) =
      residueBits (((BoundedFullSampleJointCoordinate.polynomial F w bits (pull u) (pivot (pull u)) (coordinate u)).coeff j : ℤ) :
        ZMod (Nat.fromBitsLE m + 1)) := by
  generalize hz : pair (pair u m) (BinaryNatCode.encode j) = z
  have hu : pairFst (pairFst z) = u := by rw [← hz, pairFst_pair, pairFst_pair]
  have hm : pairSnd (pairFst z) = m := by rw [← hz, pairFst_pair, pairSnd_pair]
  have hj : Nat.fromBitsLE (pairSnd z) = j := by rw [← hz, pairSnd_pair, MacaulayBits.fromBits_encode]
  subst u
  subst m
  subst j
  rfl

theorem evaluator {F : Inputs} (h : F.PolyTime)
    {w : List Bool → ℕ} (hw : UnaryFn w)
    {bits pull : List Bool → List Bool} (EB : SpaceFunction bits) (hpull : pull ∈ FP)
    (pivot : (u : List Bool) → Fin (F.dim u)) (hp : BinaryFn (fun u => (pivot u).val))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (hc : UnaryFn (fun u => (coordinate u).val))
    (htP : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c)
    (htS : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u) :
    SpaceFunction (value F w bits pull pivot coordinate) := by
  have hn : BinaryFn (BoundedFullSampleJointCoordinate.count F ∘ pull) :=
    (BoundedFullSampleJointCoordinate.count_binary h).comp hpull
  have E := PolynomialTrailingCoefficientBits.evaluator _ (reader h hw EB hpull pivot hp coordinate hc htP htS)
    hn hn ((BoundedFullSampleJointCoordinate.coefficientBits_binary h hw).comp hpull)
    (fun u => (characteristic_degree F w bits pull pivot coordinate u).le)
    (characteristic_inner_degree F w bits pull pivot coordinate)
    (characteristic_coefficient_bits F w bits pull pivot coordinate)
  exact E.congr (funext fun q => by
    unfold PolynomialTrailingCoefficientBits.value value
    rw [lowest_eq])

end LeanCanny.Encoding.BoundedFullSampleJointCoordinateCoefficient
