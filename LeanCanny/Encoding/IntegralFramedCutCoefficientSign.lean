/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutCoefficientSpace
/-! # Native full relative coefficient signs at the same successor vertex

The complete square sampler uses actual current-Q creating companions.
Every test coefficient uses the full relative factor at the selected
choice, independently of the recorded truncation degree. Both costs are
derived from original controls and their verified bounds.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutCoefficientTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCutProbeTaskBits (parameters)
open IntegralMixedFramedCutProbeTransportBits (plan data)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (a : Access P) (D : Plan P)
  (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
  (hFpos : ∀ root,1≤F root)
  (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
  (h : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C))
  (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D H L F C) h)

include a hL hF hC h hb in
theorem test_access : (test P D H L F C hs hFpos hf).Access where
  degree := degree_binary P a D H
  mass := mass_binary P a D H L F C hL hF hC
  coefficient := coefficient_evaluator P a D H L F C hs hL hF hC hFpos hf h hb

noncomputable def value : List Bool→List Bool :=
  SquareSampleCompleteIndexedPolynomialTest.value (IntegralFramedCutSuccessor.input P D H L F C hs)
    (test P D H L F C hs hFpos hf)

include a hL hF hC h hb in
theorem evaluator
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D))
    (hc : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew)
    (hbc : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew hc) :
    SpaceFunction (value P D H L F C hs hFpos hf) :=
  SquareSampleCompleteIndexedPolynomialTest.evaluator
    (IntegralFramedCutSuccessor.access P a D H Hnew hc hbc L F C hs hL hF hC)
    (test_access P a D H L F C hs hL hF hC hFpos hf h hb)

omit a hL hF hC h hb in
 theorem polynomial_eval (c d : List Bool)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
    (z : Fin ((IntegralFramedCutSuccessor.input P D H L F C hs).count c)→ℝ) :
    (polynomial P D H L F C hs c d).eval₂ (Int.castRingHom ℝ) z=
      (IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H (query P (pair c d))).eval₂ (Int.castRingHom ℝ)
        (fun i=>z (Fin.cast (dimension_pair P D H L F C hs c d ha) i.succ)) := by
  rw [polynomial,dite_eq_left ha,MvPolynomial.eval₂_rename,MvPolynomial.eval₂_rename]
  rfl

omit a hL hF hC h hb in
 theorem packet (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCutSuccessor.input P D H L F C hs) c w)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P c) :
    value P D H L F C hs hFpos hf (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign ((IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H (query P (pair c d))).eval₂
        (Int.castRingHom ℝ) (fun i=>(SquareSampleCompleteVertices.candidate
          (IntegralFramedCutSuccessor.input P D H L F C hs) c w hv).val
            (Fin.cast (dimension_pair P D H L F C hs c d ha) i.succ)))) := by
  rw [value,SquareSampleCompleteIndexedPolynomialTest.packet _ _ c w d hv]
  exact congrArg (fun x:ℝ=>InfinitesimalSign.encode (SignType.sign x)) (polynomial_eval P D H L F C hs c d ha _)

end LeanCanny.Encoding.IntegralFramedCutCoefficientTest
