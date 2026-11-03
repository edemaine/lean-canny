/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.BoundedRegularIntegerCurrentQPlanned
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackBounds
/-! # Root-lifted original controls retain an already-derived modulus budget -/
@[expose] public section
namespace LeanCanny.Algebra.BoundedRegularIntegerCurrentQBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem requiredModulus_pullback (P : Parameters) (project : List Bool → List Bool) (extra L F C : List Bool → ℕ)
    (root : List Bool) :
    IntegralMixedFramedNormalizationBits.requiredModulus (IntegralMixedFramedRootPullback.parameters P project extra)
      (L∘project) (F∘project) (C∘project) root=
      IntegralMixedFramedNormalizationBits.requiredModulus P L F C (project root) := rfl

noncomputable def pullbackControls (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Original P D J)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (project : List Bool → List Bool) (hp : project∈FP) (extra : List Bool → ℕ) (he : BinaryFn extra)
    (L F C : List Bool → ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) :=
  controls (IntegralMixedFramedRootPullback.parameters P project extra)
    (IntegralMixedFramedRootPullback.access P a project hp extra he)
    (IntegralMixedFramedRootPullback.plan P D project extra) (IntegralMixedFramedRootPullback.data P D J project extra)
    (s.pullback project hp extra) (IntegralMixedFramedRootPullback.tables T project)
    (IntegralMixedFramedRootPullback.tablesAccess T ht project hp)
    (IntegralMixedFramedRootPullback.represents P D J T hr project extra)
    (L∘project) (F∘project) (C∘project) (hL.comp hp) (hF.comp hp) (hC.comp hp)

theorem pullbackBounds (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Original P D J)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (project : List Bool → List Bool) (hp : project∈FP) (extra : List Bool → ℕ) (he : BinaryFn extra)
    (L F C : List Bool → ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (hi : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hf : ∀root,1≤F root) (hl : ∀root,1≤L root)
    (hm : ∀root,IntegralMixedFramedNormalizationBits.requiredModulus P L F C root≤P.modulusBound root) :
    IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedRootPullback.parameters P project extra)
      (IntegralMixedFramedRootPullback.plan P D project extra) (IntegralMixedFramedRootPullback.data P D J project extra)
      (pullbackControls P a D J s T ht hr project hp extra he L F C hL hF hC) where
  original:=IntegralMixedFramedRootPullback.familyInputs P D project extra L F C hi
  factor root:=hf (project root)
  fallback:=IntegralMixedFramedZeroRulesBits.fallback_bounds _ _ _ (s.zero.pullback project extra)
    (L∘project) (C∘project) (fun root=>hl (project root))
  modulus root:=(hm (project root)).trans (le_max_left _ _)

end LeanCanny.Algebra.BoundedRegularIntegerCurrentQBits
