/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeProjectionEncoding
public import LeanCanny.Encoding.FixedWidthQuery
public import LeanCanny.Algebra.EmbeddedMonomialCoefficient

/-! # Direction patterns for projection coefficient queries

A level or unshifted derivative requires zero direction exponents. The second
term of a partial row requires exactly one selected direction variable.
These tests leave point and parameter exponents unrestricted.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeProjectionQuery

open LeanCanny.Encoding
open Geometry TubeEncoding TubeProjectionEncoding
open LeanCanny.Algebra

noncomputable def exponent (n W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) : Variable (n c) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => FixedWidthQuery.coordinate W target c (variableEquiv (n c) j).val)

noncomputable def shiftVector (n : ℕ) : Option (Point n) → Variable n →₀ ℕ
  | none => 0
  | some i => Finsupp.single (.inl (.inr i)) 1

def expected (r : Option ℕ) (i : ℕ) : ℕ := if r = some i then 1 else 0

def Pattern (n W : List Bool → ℕ) (target : List Bool → List Bool) (r : List Bool → Option ℕ) (c : List Bool) : Prop :=
  ∀ i < pointCount (n c), FixedWidthQuery.coordinate W target c (pointCount (n c) + i) = expected (r c) i

theorem shiftVector_embedding (n : ℕ) (s : Option (Point n)) (j : Coordinate n) :
    shiftVector n s (ProjectionFlatten.coefficientEmbedding j) = 0 := by
  cases s <;> cases j <;> simp [shiftVector, ProjectionFlatten.coefficientEmbedding]

theorem shiftVector_direction (n : ℕ) (s : Option (Point n)) (i : Point n) :
    shiftVector n s (.inl (.inr i)) = expected (s.map (fun j => (pointEquiv n j).val)) (pointEquiv n i).val := by
  cases s with
  | none => simp [shiftVector, expected]
  | some j =>
    have he : (pointEquiv n j).val = (pointEquiv n i).val ↔ j = i := by
      constructor
      · intro h
        exact (pointEquiv n).injective (Fin.ext h)
      · rintro rfl
        rfl
    simp [shiftVector, expected, he, Finsupp.single_apply]

theorem pattern_iff (n W : List Bool → ℕ) (target : List Bool → List Bool) (r : List Bool → Option ℕ)
    (c : List Bool) (s : Option (Point (n c))) (hs : r c = s.map (fun j => (pointEquiv (n c) j).val)) :
    ((exponent n W target c).comapDomain ProjectionFlatten.coefficientEmbedding
      ProjectionFlatten.coefficientEmbedding_injective.injOn).mapDomain ProjectionFlatten.coefficientEmbedding + shiftVector (n c) s =
        exponent n W target c ↔ Pattern n W target r c := by
  rw [EmbeddedCoefficient.embedding_pattern_iff _ ProjectionFlatten.coefficientEmbedding_injective _ _ (shiftVector_embedding (n c) s)]
  constructor
  · intro h i hi
    let j := (pointEquiv (n c)).symm ⟨i, hi⟩
    have hj : (.inl (.inr j) : Variable (n c)) ∉ Set.range ProjectionFlatten.coefficientEmbedding := by
      rintro ⟨u, hu⟩
      cases u <;> cases hu
    have he := h (.inl (.inr j)) hj
    simpa only [exponent, Finsupp.coe_equivFunOnFinite_symm, index_direction, shiftVector_direction,
      j, Equiv.apply_symm_apply, hs] using he
  · intro h j hj
    rcases j with (i | i) | p
    · exact False.elim (hj ⟨.inl i, rfl⟩)
    · simpa only [exponent, Finsupp.coe_equivFunOnFinite_symm, index_direction, shiftVector_direction, hs] using
        h (pointEquiv (n c) i).val (pointEquiv (n c) i).isLt
    · exact False.elim (hj ⟨.inr p, rfl⟩)

end LeanCanny.ETR.TubeProjectionQuery
