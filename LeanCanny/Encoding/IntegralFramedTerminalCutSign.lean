/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalCutSpace
/-! # Original-only selected-cut coefficient signs on one terminal joint root

The complete terminal sampler and full factor probes both come from the
proved current-Q native machines. Every indexed choice/coefficient test
retains the same complete vertex. No square, factor or sign evaluator is
an input.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCutProbeTaskBits (parameters)
open IntegralMixedFramedCutProbeTransportBits (plan data)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q)
  (key : List Bool→List Bool) (hpos : ∀ q,0<(family P D H).birth (key q))

noncomputable def test := SquareSampleCompleteSuffixPolynomialTest.test (source P D H L F C hs key hpos hFpos hf)
noncomputable def value := SquareSampleCompleteIndexedPolynomialTest.value
  (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) (test P D H L F C hs hFpos hf key hpos)

theorem evaluator (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) (hk : key∈FP)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D H L F C) h)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D))
    (hc : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew)
    (hbc : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew hc) :
    SpaceFunction (value P D H L F C hs hFpos hf key hpos) :=
  SquareSampleCompleteSuffixPolynomialTest.evaluator
    (IntegralFramedCurrentQSquare.access_native P a D H Hnew hc hbc L F C hs hL hF hC key hk hpos)
    (source P D H L F C hs key hpos hFpos hf)
    (access P a D H L F C hs hL hF hC hFpos hf key hk hpos h hb)

theorem packet (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w) :
    value P D H L F C hs hFpos hf key hpos (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign ((polynomial P D H key c d).eval₂ (Int.castRingHom ℝ) (fun i=>
        (SquareSampleCompleteVertices.candidate (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w hv).val
          (Fin.cast ((source P D H L F C hs key hpos hFpos hf).dimension c d)
            (FixedWidthSuffixLiftBits.shift (count P D H key c-arity P D H key c d) i))))) :=
  SquareSampleCompleteSuffixPolynomialTest.packet (source P D H L F C hs key hpos hFpos hf) c w d hv

end LeanCanny.Encoding.IntegralFramedTerminalCutTest
