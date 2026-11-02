/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullNativeSpace
public import LeanCanny.Algebra.IntegralMixedFullHeightSyntax
public import LeanCanny.Algebra.IntegralMixedHeaderMetadata
/-! # Original syntax and source ceilings supply the complete arithmetic controls

Integer degree and coefficient operations in the core are charged in space.
Header writers and their literal representation remain original-input frontend
obligations, as do the core's original scalar and low-coefficient primitives.
No current matrix, bank, or recursive answer evaluator is a cost premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask

noncomputable def controls_of_original (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (core : IntegralMixedFullCoreBits.Controls P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedHeaderTablesBits.Represents P D T) (C L : List Bool → ℕ)
    (hi : IntegralMixedFullHeightBits.Inputs P D C L) (hC : BinaryFn C) (hL : BinaryFn L)
    (hm : ∀ root, 2 * IntegralMixedNormalizationTopBits.characteristicBudget P
      (IntegralMixedFullHeightBits.height P C L) root + 4 ≤ P.modulusBound root) : Controls P D where
  arithmetic := IntegralMixedFullHeightBits.controls P a D core C L hi hC hL hm
  kind := IntegralMixedHeaderTablesBits.rawMetadata P a D T ht hr

theorem model_space_of_original (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (core : IntegralMixedFullCoreBits.Controls P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedHeaderTablesBits.Represents P D T) (C L : List Bool → ℕ)
    (hi : IntegralMixedFullHeightBits.Inputs P D C L) (hC : BinaryFn C) (hL : BinaryFn L)
    (hm : ∀ root, 2 * IntegralMixedNormalizationTopBits.characteristicBudget P
      (IntegralMixedFullHeightBits.height P C L) root + 4 ≤ P.modulusBound root) :
    SpaceFunction (machine P a D (controls_of_original P a D core T ht hr C L hi hC hL hm)).model :=
  model_space P a D (controls_of_original P a D core T ht hr C L hi hC hL hm)

end LeanCanny.Algebra.IntegralMixedFullNativeBits
