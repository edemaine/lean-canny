/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualQuery
public import LeanCanny.Algebra.IntegralMixedCutQueries
/-! # Coordinate cut entries are actual virtual critical coefficients

The same selected old parent, formal nilpotent digit, and both old-basis
indices occur on the two sides. This identifies the concrete lower stage
for coordinate factors without assuming a normalized coefficient reader.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCoordinateNativeBridge
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedCutSource IntegralMixedVirtualSweepSource IntegralMixedVirtualQueryBits
set_option backward.isDefEq.respectTransparency false

structure Selection (F : Family) where
  coordinate : (q : List Bool) → Fin (F.ambient q - (F.rule q).critical.offset.val + 1)
  coefficient : (q : List Bool) → Fin (IntegralMixedCoordinateTrailing.ChoiceBound (F.spatial q) (F.rule q))
  kind : ∀ q, F.kind q = .coordinate (coordinate q) (coefficient q)

noncomputable abbrev family (F : Family) := pull F PaddedIntegralGeneratorSource.base

noncomputable def indices (F : Family) (s : Selection F) : Indices (family F) where
  coordinate q := s.coordinate (PaddedIntegralGeneratorSource.base q)
  coefficientIndex q := (s.coefficient (PaddedIntegralGeneratorSource.base q)).val
  target _ := 0
  row := IntegralMixedCutQueries.index F PaddedIntegralGeneratorSource.row
  col := IntegralMixedCutQueries.index F PaddedIntegralGeneratorSource.col
  modulus q := Nat.fromBitsLE (PaddedIntegralGeneratorSource.modulus q) + 1
  modulus_ne_zero _ := Nat.succ_ne_zero _

noncomputable abbrev source (F : Family) (s : Selection F) :=
  IntegralMixedVirtualSweepSource.source (family F) (indices F s)

theorem value_eq (F : Family) (s : Selection F) (q : List Bool) :
    (source F s).value q = IntegralMixedCutQueries.value F q := by
  rw [IntegralMixedVirtualSweepSource.value_eq]
  unfold IntegralMixedCutQueries.value
  rw [s.kind]
  rfl

theorem metadata (F : Family) (s : Selection F) (h : InputMetadata F)
    (hj : BinaryFn (fun q => (s.coordinate q).val))
    (hk : BinaryFn (fun q => (s.coefficient q).val)) :
    IntegralMixedVirtualNativeBits.Metadata (family F) (indices F s) := by
  have HB := PaddedIntegralGeneratorSource.base_FP
  have HR : BinaryFn (fun q => count (F.birth (PaddedIntegralGeneratorSource.base q) + 1)
      (F.width (PaddedIntegralGeneratorSource.base q))) :=
    (((BinaryFn.const 2).powUnary h.width).powUnary (h.birth.add (UnaryFn.const 1))).comp HB
  exact {
    ambient := h.ambient.comp HB
    birth := h.birth.comp HB
    width := h.width.comp HB
    offset := h.offset.comp HB
    degree := h.degree.comp HB
    objective := h.objective.comp HB
    target := BinaryFn.const 0
    row := (BinaryFn.fromBits PaddedIntegralGeneratorSource.row_FP).mod HR
    col := (BinaryFn.fromBits PaddedIntegralGeneratorSource.col_FP).mod HR
    modulus := (BinaryFn.fromBits PaddedIntegralGeneratorSource.modulus_FP).add (BinaryFn.const 1)
    coordinate := hj.comp HB
    coefficientIndex := hk.comp HB }

end LeanCanny.Algebra.IntegralMixedCoordinateNativeBridge
