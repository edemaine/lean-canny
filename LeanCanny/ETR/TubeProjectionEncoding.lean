/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeEncoding
public import LeanCanny.Algebra.ProjectionCoefficientFormula

/-! # Coordinate layout for the integer tube projection systems

Point and root-shift coordinates form the first block; their direction
coordinates form the second. Alpha, epsilon, and delta follow both blocks.
The tube embedding preserves the first block and moves the parameter block.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeProjectionEncoding
open Geometry TubeEncoding
open LeanCanny.Algebra

abbrev Point (n : ℕ) := TubePolynomial.Coordinate (Fin n)
abbrev Variable (n : ℕ) := TubePolynomial.IntegerProjectionVariable (Fin n)

def pointCount (n : ℕ) : ℕ := n + constraintCount n

def dimension (n : ℕ) : ℕ := pointCount n + pointCount n + 3

def pointEquiv (n : ℕ) : Point n ≃ Fin (pointCount n) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) (constraintEquiv n)).trans finSumFinEquiv

def variableEquiv (n : ℕ) : Variable n ≃ Fin (dimension n) :=
  (Equiv.sumCongr ((Equiv.sumCongr (pointEquiv n) (pointEquiv n)).trans finSumFinEquiv)
    parameterEquiv).trans finSumFinEquiv

@[simp] theorem index_point (n : ℕ) (i : Point n) :
    (variableEquiv n (.inl (.inl i))).val = (pointEquiv n i).val := rfl

@[simp] theorem index_direction (n : ℕ) (i : Point n) :
    (variableEquiv n (.inl (.inr i))).val = pointCount n + (pointEquiv n i).val := rfl

@[simp] theorem index_parameter (n : ℕ) (p : TubePolynomial.Parameter) :
    (variableEquiv n (.inr p)).val = pointCount n + pointCount n + (parameterEquiv p).val := rfl

@[simp] theorem tube_index_point (n : ℕ) (i : Point n) :
    (coordinateEquiv n (.inl i)).val = (pointEquiv n i).val := rfl

@[simp] theorem tube_index_parameter (n : ℕ) (p : TubePolynomial.Parameter) :
    (coordinateEquiv n (.inr p)).val = pointCount n + (parameterEquiv p).val := rfl

/-- Location in a projection query of a tube coordinate. -/
def embeddedIndex (n i : ℕ) : ℕ := if i < pointCount n then i else i + pointCount n

theorem index_embedding (n : ℕ) (j : Coordinate n) :
    (variableEquiv n (ProjectionFlatten.coefficientEmbedding j)).val =
      embeddedIndex n (coordinateEquiv n j).val := by
  cases j with
  | inl i => simp [ProjectionFlatten.coefficientEmbedding, embeddedIndex, (pointEquiv n i).isLt]
  | inr p =>
    change pointCount n + pointCount n + (parameterEquiv p).val =
      if pointCount n + (parameterEquiv p).val < pointCount n then
        pointCount n + (parameterEquiv p).val
      else pointCount n + (parameterEquiv p).val + pointCount n
    split_ifs <;> omega

theorem embeddedIndex_lt (n i : ℕ) (hi : i < TubeEncoding.dimension n) :
    embeddedIndex n i < dimension n := by
  unfold embeddedIndex TubeEncoding.dimension dimension pointCount at *
  split_ifs <;> omega

theorem range_iff (n : ℕ) (j : Variable n) :
    j ∈ Set.range (ProjectionFlatten.coefficientEmbedding (σ := Point n) (τ := TubePolynomial.Parameter)) ↔
      (variableEquiv n j).val < pointCount n ∨ pointCount n + pointCount n ≤ (variableEquiv n j).val := by
  rcases j with (i | i) | p
  · simp only [index_point]
    exact ⟨fun _ => Or.inl (pointEquiv n i).isLt, fun _ => ⟨.inl i, rfl⟩⟩
  · constructor
    · rintro ⟨j, h⟩
      cases j <;> cases h
    · intro h
      simp only [index_direction] at h
      have hi := (pointEquiv n i).isLt
      omega
  · simp only [index_parameter]
    exact ⟨fun _ => Or.inr (by omega), fun _ => ⟨.inr p, rfl⟩⟩

end LeanCanny.ETR.TubeProjectionEncoding
