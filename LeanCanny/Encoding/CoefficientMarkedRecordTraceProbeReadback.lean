/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeEvaluation
public import LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSemantics
/-! # Literal historical coefficient signs on one complete physical word -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeReadback
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem task_key (B : IntegralFramedBankQuery.Bank)
    (hkey : ∀ c, B.key c = B.key (pair (pairFst c) [])) (c u : List Bool) :
    IntegralFramedPhysicalTraceCutSource.taskKey B (IntegralFramedPhysicalTraceCutSource.parent B c u) = B.key c := by
  unfold IntegralFramedPhysicalTraceCutSource.taskKey IntegralFramedPhysicalTraceCutSource.parent
  rw [IntegralFramedTraceCutTask.task_root, pairFst_pair]
  exact (hkey c).symm

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

/-- This is the actual native reader, with no coefficient interpretation or
old-generator homomorphism supplied by its caller. -/
theorem value (B : IntegralFramedBankQuery.Bank)
    (hkey : ∀ c, B.key c = B.key (pair (pairFst c) []))
    (hFpos : ∀ root, 1 ≤ B.factor root)
    (hf : ∀ q, IntegralMixedFramedOriginalBounds.FallbackBounds B.parameters B.plan B.data B.nodes B.seed q)
    (T : IntegralMixedHeaderTablesBits.Tables)
    (ht : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (c w u : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    (hroot : pairFst (IntegralMixedVirtualTaskBits.saved B.parameters
      (IntegralFramedPhysicalTraceCutSource.parent B c u)) = pairFst (B.key c))
    (e k : ℕ)
    (hc : IntegralMixedFramedFullCutProbeBits.Active B.parameters (IntegralFramedPhysicalTraceCutSource.parent B c u))
    (he : e ≤ 2^B.parameters.width (RankedHistoryTask.root (IntegralFramedPhysicalTraceCutSource.parent B c u)))
    (hk : k ≤ 2^B.parameters.width (RankedHistoryTask.root (IntegralFramedPhysicalTraceCutSource.parent B c u)))
    (hfit : (family B.parameters B.plan B.data).birth (IntegralMixedVirtualTaskBits.saved B.parameters
      (IntegralFramedPhysicalTraceCutSource.parent B c u)) ≤ (family B.parameters B.plan B.data).birth (B.key c)) :
    IntegralFramedPhysicalTraceCutSource.value B hkey hFpos hf T ht
      (pair (pair c w) (IntegralFramedPhysicalTraceCutSource.datum u e k)) =
    InfinitesimalSign.encode (SignType.sign
      ((CoefficientMarkedRecordTraceProbePhysical.polynomial B.parameters B.plan B.data
        (IntegralMixedVirtualTaskBits.saved B.parameters (IntegralFramedPhysicalTraceCutSource.parent B c u)) k e).eval₂
          (Int.castRingHom ℝ) (CoefficientFinitePhysicalQuery.natural
            (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hw).val))) := by
  let p := IntegralFramedPhysicalTraceCutSource.parent B c u
  let d := IntegralFramedPhysicalTraceCutSource.datum u e k
  have hp : pairFst (IntegralFramedPhysicalTraceCutSource.reindex B (pair c d)) = p := by
    rw [IntegralFramedPhysicalTraceCutSource.reindex_packet, pairFst_pair]
  have hs : pairSnd (IntegralFramedPhysicalTraceCutSource.reindex B (pair c d)) =
      pair (BinaryNatCode.encode e) (BinaryNatCode.encode k) := by
    rw [IntegralFramedPhysicalTraceCutSource.reindex_packet, pairSnd_pair]
  rw [IntegralFramedPhysicalTraceCutSource.packet_fields B hkey hFpos hf T ht c w hw d p _ hp hs]
  apply congrArg (fun v : ℝ => InfinitesimalSign.encode (SignType.sign v))
  have hfitting : IntegralFramedTerminalCutTest.oldArity B.parameters B.plan B.data p
      (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)) ≤
      IntegralFramedTerminalCutTest.count B.parameters B.plan B.data
        (IntegralFramedPhysicalTraceCutSource.taskKey B) p := by
    rw [IntegralFramedTerminalCutTest.oldArity_parent]
    change (family B.parameters B.plan B.data).birth (IntegralMixedVirtualTaskBits.saved B.parameters p) ≤
      (family B.parameters B.plan B.data).birth (IntegralFramedPhysicalTraceCutSource.taskKey B p)
    rw [show IntegralFramedPhysicalTraceCutSource.taskKey B p = B.key c from task_key B hkey c u]
    exact hfit
  have h := CoefficientMarkedRecordTraceProbeEvaluation.terminal_at_later B T ht
    (IntegralFramedPhysicalTraceCutSource.taskKey B) p c w hw (task_key B hkey c u) hroot e k hc he hk hfitting
  unfold IntegralFramedPhysicalTraceCutSource.oldSource
  simp only [IntegralFramedTerminalCutTest.source]
  exact h

end LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeReadback
