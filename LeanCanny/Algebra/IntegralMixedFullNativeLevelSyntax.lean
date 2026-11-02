/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullNativeSyntax
public import LeanCanny.Algebra.FermatLevelOriginalHeight

/-! # Complete arithmetic for level lifts with implicitly large coefficients

An original binary exponent supplies the level coefficient 2^E. The native
coefficient reader and its height ceiling are derived from that exponent and
the old polynomial word. The remaining scalar and integer controls concern
original cells only; no recursive critical or matrix reader is a premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask

noncomputable def levelHeight (word : List Bool → List Bool) (E : List Bool → ℕ) :=
  FermatLevelOriginalHeight.height (fun r => ETR.TermView.term (word r)) E

theorem core_of_level_syntax (P : Parameters) (a : Access P)
    (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedHeaderTablesBits.Represents P D T)
    (scalar : IntegralMixedFullScalarBits.Controls P D)
    (integer : IntegralMixedIntegerProducerSpaceBits.Original P D)
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ r, (ETR.TermView.term (word r)).arity ≤ P.ambient r)
    (E : List Bool → ℕ) (hE : BinaryFn E)
    (hlow : ∀ r, (D.spatial r).low = FermatLevelCoefficientBits.polynomial P.ambient
      (FermatLevelOriginalSpatialBits.old P word) (FermatLevelPowerResidue.coefficient E) r) :
    IntegralMixedFullCoreBits.Controls P D :=
  let full := IntegralMixedHeaderTablesBits.fullMetadata P a D T ht hr
  let physical := IntegralMixedHeaderTablesBits.physicalInputMetadata P a D T ht hr
  { scalar := scalar
    algebra := {
      critical := FermatLevelPowerResidue.controls P a D full physical word hword hs E hE hlow
      producer := { full := full, physical := physical, integer := integer } } }

noncomputable def controls_of_level_syntax (P : Parameters) (a : Access P)
    (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedHeaderTablesBits.Represents P D T)
    (scalar : IntegralMixedFullScalarBits.Controls P D)
    (integer : IntegralMixedIntegerProducerSpaceBits.Original P D)
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ r, (ETR.TermView.term (word r)).arity ≤ P.ambient r)
    (E : List Bool → ℕ) (hE : BinaryFn E) (L : List Bool → ℕ) (hL : BinaryFn L)
    (hlow : ∀ r, (D.spatial r).low = FermatLevelCoefficientBits.polynomial P.ambient
      (FermatLevelOriginalSpatialBits.old P word) (FermatLevelPowerResidue.coefficient E) r)
    (hl : ∀ r, (D.spatial r).leading.natAbs.size ≤ levelHeight word E r)
    (hc : ∀ r, ∀ c ∈ D.rules r, IntegralMixedFullScriptHeight.CommandBounds (levelHeight word E r) (L r) c)
    (hf : ∀ key, IntegralMixedFullHeightBits.RuleBounds (levelHeight word E (pairFst key))
      (L (pairFst key)) (D.fallback key).rule)
    (hm : ∀ root, 2 * IntegralMixedNormalizationTopBits.characteristicBudget P
      (IntegralMixedFullHeightBits.height P (levelHeight word E) L) root + 4 ≤ P.modulusBound root) : Controls P D :=
  controls_of_original P a D (core_of_level_syntax P a D T ht hr scalar integer word hword hs E hE hlow)
    T ht hr (levelHeight word E) L
    (FermatLevelOriginalHeight.word_inputs P D word E L hlow hl hc hf)
    (FermatLevelOriginalHeight.word_height_binary word E hword hE) hL hm

theorem model_space_of_level_syntax (P : Parameters) (a : Access P)
    (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedHeaderTablesBits.Represents P D T)
    (scalar : IntegralMixedFullScalarBits.Controls P D)
    (integer : IntegralMixedIntegerProducerSpaceBits.Original P D)
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ r, (ETR.TermView.term (word r)).arity ≤ P.ambient r)
    (E : List Bool → ℕ) (hE : BinaryFn E) (L : List Bool → ℕ) (hL : BinaryFn L)
    (hlow : ∀ r, (D.spatial r).low = FermatLevelCoefficientBits.polynomial P.ambient
      (FermatLevelOriginalSpatialBits.old P word) (FermatLevelPowerResidue.coefficient E) r)
    (hl : ∀ r, (D.spatial r).leading.natAbs.size ≤ levelHeight word E r)
    (hc : ∀ r, ∀ c ∈ D.rules r, IntegralMixedFullScriptHeight.CommandBounds (levelHeight word E r) (L r) c)
    (hf : ∀ key, IntegralMixedFullHeightBits.RuleBounds (levelHeight word E (pairFst key))
      (L (pairFst key)) (D.fallback key).rule)
    (hm : ∀ root, 2 * IntegralMixedNormalizationTopBits.characteristicBudget P
      (IntegralMixedFullHeightBits.height P (levelHeight word E) L) root + 4 ≤ P.modulusBound root) :
    SpaceFunction (machine P a D
      (controls_of_level_syntax P a D T ht hr scalar integer word hword hs E hE L hL hlow hl hc hf hm)).model :=
  model_space P a D
    (controls_of_level_syntax P a D T ht hr scalar integer word hword hs E hE L hL hlow hl hc hf hm)

end LeanCanny.Algebra.IntegralMixedFullNativeBits
