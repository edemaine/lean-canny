/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSquarefreeHeightBounds
public import LeanCanny.Algebra.IntegralMixedValueHeightBounds
public import LeanCanny.Algebra.IntegralMixedNormalizationTopSource
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateBounds
/-! # One original-source coefficient ceiling for all actual raw-cut kinds -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedAllRawHeightBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource IntegralMixedCoordinateBounds
open IntegralMixedVirtualSweepSource
open scoped Classical

noncomputable def legacyHeight (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool) : ℕ :=
  max (IntegralMixedVirtualCoordinateBounds.height F H q)
    (max (IntegralMixedSquarefreeHeightBounds.height (F.ambient q) (H.rank q) (H.sourceWidth q)
      (H.spatialDegree q) (F.cap q) (H.nodes q) (H.bankHeight q))
      (IntegralMixedValueHeightBounds.height F I H q))

noncomputable def height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool) : ℕ :=
  max (legacyHeight F I H q)
    (IntegralMixedLimitCoordinateBounds.height (F.ambient q) (H.rank q) (H.sourceWidth q)
      (H.spatialDegree q) (F.cap q) (H.nodes q) (H.bankHeight q))

theorem value_height_independent (F : Family) (I J : Indices F) (H : OriginalBounds F) (q : List Bool) :
    IntegralMixedValueHeightBounds.height F I H q = IntegralMixedValueHeightBounds.height F J H q := rfl

theorem coefficient_height (F : Family) (I : Indices F) (H : OriginalBounds F)
    (q : List Bool) (k : ℕ) (u v : Fin (count (F.birth q) (F.width q))) :
    (IntegralMixedCutMatrix.coefficientMatrix (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) k u v).natAbs ≤
      2 ^ height F I H q := by
  have HL : legacyHeight F I H q ≤ height F I H q := le_max_left _ _
  cases hk : F.kind q with
  | coordinate j c =>
    let J := IntegralMixedVirtualCoordinateBounds.select F I j.val
    have HJ : J.coordinate q = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
    have HE := IntegralMixedCoordinateBounds.coefficient_height F J H.bankHeight H.sourceHeight H.bank H.coefficient q
      (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (H.nodes q) (H.rank_bound q) (H.width_bound q)
      (H.degree_bound q) (H.leading q) (H.expression_nodes q) (H.expression_coefficients q) (H.scales q)
      (H.slope q) (H.source_le_bank q) c k u v
    rw [HJ] at HE
    exact HE.trans (Nat.pow_le_pow_right (by decide) ((le_max_left _ _).trans HL))
  | squarefree j c =>
    let J := IntegralMixedVirtualCoordinateBounds.select F I j.val
    have HJ : J.coordinate q = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
    have HE := IntegralMixedSquarefreeHeightBounds.coefficient_height F J H q c k u v
    rw [HJ] at HE
    exact HE.trans (Nat.pow_le_pow_right (by decide) (((le_max_left _ _).trans (le_max_right _ _)).trans HL))
  | value j c =>
    let J := IntegralMixedVirtualCoordinateBounds.select F I j.val
    have HJ : J.coordinate q = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
    have HE := IntegralMixedValueHeightBounds.coefficient_height F J H q c k u v
    rw [HJ, value_height_independent F J I H q] at HE
    exact HE.trans (Nat.pow_le_pow_right (by decide) (((le_max_right _ _).trans (le_max_right _ _)).trans HL))
  | limitCoordinate j c =>
    let J := IntegralMixedVirtualCoordinateBounds.select F I j.val
    have HJ : J.coordinate q = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
    have HE := IntegralMixedLimitCoordinateBounds.coefficient_height F J H q c k u v
    rw [HJ] at HE
    exact HE.trans (Nat.pow_le_pow_right (by decide) (le_max_right _ _))

noncomputable def rawBounds (F : Family) (I : Indices F) (H : OriginalBounds F) : RawBounds F where
  height := height F I H
  bound := coefficient_height F I H

private theorem max_binary {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    BinaryFn (fun q => max (f q) (g q)) := by
  simpa only [max_def] using BinaryFn.ite (hf.le hg) hg hf

theorem height_binary (F : Family) (I : Indices F) (H : OriginalBounds F)
    (h : IntegralMixedVirtualNativeBits.Metadata F I) (hM : BinaryFn H.rank) (hW : UnaryFn H.sourceWidth)
    (hD : BinaryFn H.spatialDegree) (hS : BinaryFn F.cap) (hL : BinaryFn H.nodes) (hG : BinaryFn H.bankHeight) :
    BinaryFn (height F I H) :=
  max_binary (max_binary (IntegralMixedVirtualCoordinateBounds.height_binary F H h.ambient hM hW hD hS hL hG)
    (max_binary (IntegralMixedSquarefreeHeightBounds.height_binary h.ambient hM hW hD hS hL hG)
      (IntegralMixedValueHeightBounds.height_binary F I H h hM hW hD hS hL hG)))
    (IntegralMixedLimitCoordinateBounds.family_height_binary F H h.ambient hM hW hD hS hL hG)

theorem top_height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool)
    (u v : Fin (IntegralMixedNormalizationTopBits.dimension F q)) :
    (IntegralMixedNormalizationTopBits.top F q u v).natAbs ≤ 2 ^ height F I H q :=
  coefficient_height F I H q (F.degree q) u v

end LeanCanny.Algebra.IntegralMixedAllRawHeightBounds
