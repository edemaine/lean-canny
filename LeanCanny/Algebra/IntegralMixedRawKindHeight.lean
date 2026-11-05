/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedAllRawHeightBounds
/-! # The raw coefficient ceiling covers every typed query kind at the same rule

Lower-choice guard probes change the kind/choice while keeping the bank,
source and critical rule. The original height ceiling is independent of
that choice, so the actual selected-cut estimate covers these probes too.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRawKindHeight
open IntegralMixedCutSource IntegralMixedVirtualSweepSource IntegralMixedCoordinateBounds
open scoped Classical

noncomputable def withKind (F : Family) (K : ∀ q, IntegralMixedRelativeCuts.Kind (F.spatial q) (F.rule q)) : Family :=
  { F with kind := K }

noncomputable def indices (F : Family) (I : Indices F)
    (K : ∀ q, IntegralMixedRelativeCuts.Kind (F.spatial q) (F.rule q)) : Indices (withKind F K) where
  coordinate := I.coordinate
  coefficientIndex := I.coefficientIndex
  target := I.target
  row := I.row
  col := I.col
  modulus := I.modulus
  modulus_ne_zero := I.modulus_ne_zero

noncomputable def bounds (F : Family) (H : OriginalBounds F)
    (K : ∀ q, IntegralMixedRelativeCuts.Kind (F.spatial q) (F.rule q)) : OriginalBounds (withKind F K) where
  bankHeight := H.bankHeight
  sourceHeight := H.sourceHeight
  rank := H.rank
  sourceWidth := H.sourceWidth
  spatialDegree := H.spatialDegree
  nodes := H.nodes
  bank := H.bank
  coefficient := H.coefficient
  rank_bound := H.rank_bound
  width_bound := H.width_bound
  degree_bound := H.degree_bound
  leading := H.leading
  expression_nodes := H.expression_nodes
  expression_coefficients := H.expression_coefficients
  scales := H.scales
  slope := H.slope
  source_le_bank := H.source_le_bank

theorem height_eq (F : Family) (I : Indices F) (H : OriginalBounds F)
    (K : ∀ q, IntegralMixedRelativeCuts.Kind (F.spatial q) (F.rule q)) (q : List Bool) :
    IntegralMixedAllRawHeightBounds.height (withKind F K) (indices F I K) (bounds F H K) q =
      IntegralMixedAllRawHeightBounds.height F I H q := rfl

theorem coefficient_height (F : Family) (I : Indices F) (H : OriginalBounds F)
    (K : ∀ q, IntegralMixedRelativeCuts.Kind (F.spatial q) (F.rule q)) (q : List Bool) (tau : ℕ)
    (i j : Fin (FixedWidthPolynomial.count (F.birth q) (F.width q))) :
    (IntegralMixedCutMatrix.coefficientMatrix (F.state q) (F.birth_bound q) (F.rule q) (K q) tau i j).natAbs ≤
      2 ^ IntegralMixedAllRawHeightBounds.height F I H q :=
  IntegralMixedAllRawHeightBounds.coefficient_height (withKind F K) (indices F I K) (bounds F H K) q tau i j

/-- No family of query choices is an input to this pointwise estimate. -/
theorem coefficient_height_at (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool)
    (Kq : IntegralMixedRelativeCuts.Kind (F.spatial q) (F.rule q)) (tau : ℕ)
    (i j : Fin (FixedWidthPolynomial.count (F.birth q) (F.width q))) :
    (IntegralMixedCutMatrix.coefficientMatrix (F.state q) (F.birth_bound q) (F.rule q) Kq tau i j).natAbs ≤
      2 ^ IntegralMixedAllRawHeightBounds.height F I H q := by
  let K (z : List Bool) : IntegralMixedRelativeCuts.Kind (F.spatial z) (F.rule z) :=
    if hz : z = q then (by subst z; exact Kq) else F.kind z
  have HK : K q = Kq := by simp only [K, dite_eq_left rfl]
  simpa only [HK] using coefficient_height F I H K q tau i j

end LeanCanny.Algebra.IntegralMixedRawKindHeight
