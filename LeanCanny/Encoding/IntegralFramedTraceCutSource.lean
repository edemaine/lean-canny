/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTraceCutMetadata
public import LeanCanny.Encoding.SquareSampleCompleteSuffixSourceReindex
public import LeanCanny.Encoding.IntegralFramedTerminalCutSpace
/-! # Every chronological factor probe uses one fixed terminal sampler

The source context is the original root. The indexed datum contains the
cut birth and coefficient/choice selectors. Reindexing moves only the
actual integer test polynomial; it never changes the terminal vertex.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTraceCutSource
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralFramedTraceCutMetadata (terminal key terminal_positive key_positive)
open IntegralMixedFramedCutProbeTaskBits (parameters)
open IntegralMixedFramedCutProbeTransportBits (plan data)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q)

noncomputable def input := IntegralFramedCompleteSquare.input P D H L F C hs (terminal P D) (terminal_positive P D H)
noncomputable def oldSource := IntegralFramedTerminalCutTest.source P D H L F C hs (key P D) (key_positive P D H) hFpos hf

omit hFpos hf in
theorem reindex_count (r d : List Bool) :
    (IntegralFramedCompleteSquare.input P D H L F C hs (key P D) (key_positive P D H)).count
      (pairFst (IntegralFramedTraceCutTask.reindex P (pair r d)))=(input P D H L F C hs).count r := by
  change (family P D H).birth (key P D (pairFst (IntegralFramedTraceCutTask.reindex P (pair r d))))=
    (family P D H).birth (terminal P D r)
  simp only [IntegralFramedTraceCutTask.reindex,pairFst_pair,IntegralFramedTraceCutMetadata.key_task]

noncomputable def source : SquareSampleCompleteSuffixPolynomialTest.Source (input P D H L F C hs) :=
  (oldSource P D H L F C hs hFpos hf).reindex (IntegralFramedTraceCutTask.reindex P) (reindex_count P D H L F C hs)

theorem access (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D H L F C) h) :
    (source P D H L F C hs hFpos hf).Access :=
  (IntegralFramedTerminalCutTest.access P a D H L F C hs hL hF hC hFpos hf (key P D)
    (IntegralFramedTraceCutMetadata.key_FP P D H h0) (key_positive P D H) h hb).reindex
      (IntegralFramedTraceCutTask.reindex P) (IntegralFramedTraceCutTask.reindex_FP P a) (reindex_count P D H L F C hs)

noncomputable def test := SquareSampleCompleteSuffixPolynomialTest.test (source P D H L F C hs hFpos hf)
noncomputable def value := SquareSampleCompleteIndexedPolynomialTest.value (input P D H L F C hs) (test P D H L F C hs hFpos hf)

theorem evaluator (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D H L F C) h)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D))
    (hc : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew)
    (hbc : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew hc) : SpaceFunction (value P D H L F C hs hFpos hf) :=
  SquareSampleCompleteSuffixPolynomialTest.evaluator
    (IntegralFramedCurrentQSquare.access_native P a D H Hnew hc hbc L F C hs hL hF hC
      (terminal P D) (IntegralFramedTraceCutMetadata.terminal_FP P D H h0) (terminal_positive P D H))
    (source P D H L F C hs hFpos hf) (access P D H L F C hs hFpos hf a hL hF hC h0 h hb)

end LeanCanny.Encoding.IntegralFramedTraceCutSource
