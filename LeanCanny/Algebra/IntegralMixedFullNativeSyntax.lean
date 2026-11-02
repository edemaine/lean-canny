/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullNativeOriginal
public import LeanCanny.Algebra.IntegralMixedOriginalBodyTable
public import LeanCanny.Algebra.IntegralMixedOriginalSpatialLeaves
public import LeanCanny.Algebra.IntegralMixedHeaderPhysicalMetadata

/-! # Complete mixed arithmetic from original syntax and charged integer sources

The header and scalar-body writers have literal original syntax readback.
One original polynomial term supplies both physical and virtual coefficient
leaves. Integer producers may use charged space, including the constructed
initial exceptional bank. No recursive arithmetic evaluator is an input.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask

theorem core_of_syntax (P : Parameters) (a : Access P)
    (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedHeaderTablesBits.Represents P D T)
    (body : IntegralMixedOriginalRuleBodyBits.Access P D)
    (integer : IntegralMixedIntegerProducerSpaceBits.Original P D)
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ r, (ETR.TermView.term (word r)).arity ≤ P.ambient r + 1)
    (hp : ∀ r, (ETR.TermView.term (word r)).finitePolynomial (P.ambient r + 1) = (D.spatial r).low) :
    IntegralMixedFullCoreBits.Controls P D :=
  let full := IntegralMixedHeaderTablesBits.fullMetadata P a D T ht hr
  let physical := IntegralMixedHeaderTablesBits.physicalInputMetadata P a D T ht hr
  { scalar := IntegralMixedOriginalRuleBodyBits.controls P a D full physical body
    algebra := {
      critical := IntegralMixedOriginalSpatialTermBits.controls P a D full physical word hword hs hp
      producer := { full := full, physical := physical, integer := integer } } }

noncomputable def controls_of_syntax (P : Parameters) (a : Access P)
    (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedHeaderTablesBits.Represents P D T)
    (body : IntegralMixedOriginalRuleBodyBits.Access P D)
    (integer : IntegralMixedIntegerProducerSpaceBits.Original P D)
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ r, (ETR.TermView.term (word r)).arity ≤ P.ambient r + 1)
    (hp : ∀ r, (ETR.TermView.term (word r)).finitePolynomial (P.ambient r + 1) = (D.spatial r).low)
    (C L : List Bool → ℕ) (hi : IntegralMixedFullHeightBits.Inputs P D C L)
    (hC : BinaryFn C) (hL : BinaryFn L)
    (hm : ∀ root, 2 * IntegralMixedNormalizationTopBits.characteristicBudget P
      (IntegralMixedFullHeightBits.height P C L) root + 4 ≤ P.modulusBound root) : Controls P D :=
  controls_of_original P a D (core_of_syntax P a D T ht hr body integer word hword hs hp)
    T ht hr C L hi hC hL hm

theorem model_space_of_syntax (P : Parameters) (a : Access P)
    (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedHeaderTablesBits.Represents P D T)
    (body : IntegralMixedOriginalRuleBodyBits.Access P D)
    (integer : IntegralMixedIntegerProducerSpaceBits.Original P D)
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ r, (ETR.TermView.term (word r)).arity ≤ P.ambient r + 1)
    (hp : ∀ r, (ETR.TermView.term (word r)).finitePolynomial (P.ambient r + 1) = (D.spatial r).low)
    (C L : List Bool → ℕ) (hi : IntegralMixedFullHeightBits.Inputs P D C L)
    (hC : BinaryFn C) (hL : BinaryFn L)
    (hm : ∀ root, 2 * IntegralMixedNormalizationTopBits.characteristicBudget P
      (IntegralMixedFullHeightBits.height P C L) root + 4 ≤ P.modulusBound root) :
    SpaceFunction (machine P a D
      (controls_of_syntax P a D T ht hr body integer word hword hs hp C L hi hC hL hm)).model :=
  model_space P a D (controls_of_syntax P a D T ht hr body integer word hword hs hp C L hi hC hL hm)

end LeanCanny.Algebra.IntegralMixedFullNativeBits
