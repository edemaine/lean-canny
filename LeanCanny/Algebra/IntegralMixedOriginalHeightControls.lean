/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHeightFamily
public import LeanCanny.Algebra.IntegralMixedNormalizedCore
/-! # Actual normalization height controls are derived from original cells -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

theorem height_binary (P : Parameters) (a : Access P) (C L : List Bool → ℕ) (hC : BinaryFn C) (hL : BinaryFn L) :
    BinaryFn (height P C L) := by
  have HS := a.cap.add (UnaryFn.const 1)
  have HR := IntegralMixedFullScriptHeight.rank_binary HS a.width
  have HF := IntegralMixedCutHeightProfile.factor_binary a.ambient HR a.sourceWidth a.degree (BinaryFn.ofUnary HS) hL
  have HG := IntegralMixedFullScriptHeight.height_binary a.ambient HS a.width a.sourceWidth a.degree hL hC (HS.add (UnaryFn.const 1))
  exact HF.mul HG

noncomputable def controls (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (core : IntegralMixedFullCoreBits.Controls P D) (C L : List Bool → ℕ) (h : Inputs P D C L)
    (hC : BinaryFn C) (hL : BinaryFn L)
    (hm : ∀ root, 2 * IntegralMixedNormalizationTopBits.characteristicBudget P (height P C L) root + 4 ≤ P.modulusBound root) :
    IntegralMixedNormalizedCoreBits.Controls P D where
  core := core
  height := height P C L
  height_binary := height_binary P a C L hC hL
  height_bound q _ := top_height P D C L h q
  modulus_bound := hm

theorem controls_height (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (core : IntegralMixedFullCoreBits.Controls P D) (C L : List Bool → ℕ) (h : Inputs P D C L)
    (hC : BinaryFn C) (hL : BinaryFn L)
    (hm : ∀ root, 2 * IntegralMixedNormalizationTopBits.characteristicBudget P (height P C L) root + 4 ≤ P.modulusBound root) :
    (controls P a D core C L h hC hL hm).height = height P C L := rfl
end LeanCanny.Algebra.IntegralMixedFullHeightBits
