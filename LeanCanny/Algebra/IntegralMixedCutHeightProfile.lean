/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightMonotone
/-! # Original-metadata factors for one mixed relative-cut birth -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutHeightProfile
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
open IntegralMixedCutSource IntegralMixedCoordinateBounds IntegralMixedVirtualSweepSource IntegralMixedHeightScaling
set_option backward.isDefEq.respectTransparency false

def input (n S L : ℕ) := IntegralMixedCoordinateBounds.inputFactor n S L
def coordinate (n R W D S L : ℕ) := IntegralMixedCoordinateBounds.height n R W D S L 1
def row (n R W D S L : ℕ) : ℕ :=
  let T := input n S L
  IntegralFrozenConstantBounds.lowerHeight (n + 1) R W D T T T T +
    IntegralFrozenCoefficientBounds.coefficientHeight (n + 1) R W D (T + W) T T +
    (T + D * T) + W + (n + 1).size + 1
def columns (n D : ℕ) := count (n + 2) (IntegralMixedExceptionalBounds.boxWidth (n + 1) D)
def rows (n D : ℕ) := (n + 3) * columns n D
def system (n R W D S L : ℕ) := coordinate n R W D S L + row n R W D S L + 1
def value (n R W D S L : ℕ) :=
  IntegralRelativeCharacteristicBounds.determinantHeight (columns n D) R
    (IntegralMacaulayGramBounds.gramHeight (rows n D) R (system n R W D S L))
def factor (n R W D S L : ℕ) := max (coordinate n R W D S L)
  (max (IntegralPrincipalHeightBounds.height (IntegralMixedExceptionalBounds.K (n + 1) D) R (coordinate n R W D S L))
    (value n R W D S L))

theorem coordinate_scaled (n R W D S L G : ℕ) :
    IntegralMixedCoordinateBounds.height n R W D S L G = coordinate n R W D S L * G := by
  unfold coordinate IntegralMixedCoordinateBounds.height
  ring

theorem low_eq (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool) :
    IntegralMixedVirtualOriginalRowBounds.lowHeight F I H q =
      IntegralFrozenConstantBounds.lowerHeight (F.ambient q + 1) (count (F.birth q + 1) (F.width q))
        (F.spatial q).degree.size (F.spatial q).degree
        (IntegralMixedUniformVirtualInputs.height F H q) (IntegralMixedUniformVirtualInputs.height F H q)
        (IntegralMixedUniformVirtualInputs.height F H q) (IntegralMixedUniformVirtualInputs.height F H q) := rfl

theorem gradient_eq (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool) :
    IntegralMixedVirtualOriginalRowBounds.gradientHeight F I H q =
      IntegralFrozenCoefficientBounds.coefficientHeight (F.ambient q + 1) (count (F.birth q + 1) (F.width q))
        (F.spatial q).degree.size (F.spatial q).degree
        (IntegralMixedUniformVirtualInputs.height F H q + (F.spatial q).degree.size)
        (IntegralMixedUniformVirtualInputs.height F H q) (IntegralMixedUniformVirtualInputs.height F H q) := rfl

theorem row_scaled (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool) :
    IntegralMixedVirtualOriginalRowBounds.height F I H q ≤
      row (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (F.cap q) (H.nodes q) * H.bankHeight q := by
  let T := input (F.ambient q) (F.cap q) (H.nodes q)
  let G := H.bankHeight q
  have hG : 1 ≤ G := by have := H.source_le_bank q; omega
  have mult (a : ℕ) : a ≤ a * G := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left a hG
  have HL : IntegralMixedVirtualOriginalRowBounds.lowHeight F I H q ≤
      IntegralFrozenConstantBounds.lowerHeight (F.ambient q + 1) (H.rank q) (H.sourceWidth q) (H.spatialDegree q) T T T T * G := by
    rw [low_eq]
    exact (lower_mono (Nat.le_refl _) (H.rank_bound q) (H.width_bound q) (H.degree_bound q)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)).trans
        (lower_scaled _ _ _ _ T T T T G hG)
  have HC : T * G + (F.spatial q).degree.size ≤ (T + H.sourceWidth q) * G := by
    calc
      _ ≤ T * G + H.sourceWidth q * G := Nat.add_le_add_left ((H.width_bound q).trans (mult _)) _
      _ = _ := by ring
  have HG : IntegralMixedVirtualOriginalRowBounds.gradientHeight F I H q ≤
      IntegralFrozenCoefficientBounds.coefficientHeight (F.ambient q + 1) (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (T + H.sourceWidth q) T T * G := by
    rw [gradient_eq]
    exact (coefficient_mono (Nat.le_refl _) (H.rank_bound q) (H.width_bound q) (H.degree_bound q) HC (Nat.le_refl _) (Nat.le_refl _)).trans
      (coefficient_scaled _ _ _ _ (T + H.sourceWidth q) T T G hG)
  have HS : IntegralMixedVirtualOriginalRowBounds.scalarHeight F H q ≤ (T + H.spatialDegree q * T) * G := by
    change T * G + (F.spatial q).degree * (T * G) ≤ _
    calc
      _ ≤ T * G + H.spatialDegree q * (T * G) := Nat.add_le_add_left (Nat.mul_le_mul_right _ (H.degree_bound q)) _
      _ = _ := by ring
  have HW := (H.width_bound q).trans (mult (H.sourceWidth q))
  have HF := (Nat.size_le_size (Nat.add_le_add_right (Nat.sub_le (F.ambient q) (F.rule q).critical.offset.val) 1)).trans (mult (F.ambient q + 1).size)
  calc
    _ ≤ IntegralFrozenConstantBounds.lowerHeight (F.ambient q + 1) (H.rank q) (H.sourceWidth q) (H.spatialDegree q) T T T T * G +
        IntegralFrozenCoefficientBounds.coefficientHeight (F.ambient q + 1) (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (T + H.sourceWidth q) T T * G +
        (T + H.spatialDegree q * T) * G + H.sourceWidth q * G + (F.ambient q + 1).size * G + 1 * G :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add HL HG) HS) HW) HF) (mult 1)
    _ = _ := by dsimp only [row, T, G]; ring
end LeanCanny.Algebra.IntegralMixedCutHeightProfile
