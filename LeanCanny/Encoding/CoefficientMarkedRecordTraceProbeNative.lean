/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeReadback
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceCutMetadata
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutTest
/-! # Actual original historical probes on their own complete marked word -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeNative
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false


attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

theorem terminal (c : List Bool) : (B).key c = CoefficientMarkedRecordRawCutMetadata.terminal (n := n) (pairFst c) := by
  change IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n c = _
  simp only [IntegralMixedAuxiliaryMarkedRecordPlan.bankKey, CoefficientMarkedRecordRawCutMetadata.terminal,
    CoefficientMarkedRecordRowLayout.key, IntegralMixedAuxiliaryMarkedRecordPlan.fullCount,
    CoefficientMarkedPreludeActual.indices_length]

theorem parent (c : List Bool) (k : ℕ) :
    IntegralFramedPhysicalTraceCutSource.parent (B) c
      (List.replicate (CoefficientMarkedRecordCutSource.birth (n := n) (pairFst c) k) true) =
    CoefficientMarkedRecordRawCutMetadata.parent hn ht ha hR (pairFst c) k := rfl

/-- All validity, root and suffix metadata are derived from original syntax.
The word and AUX may be arbitrary, and its entire decoded tuple is retained. -/
theorem physical_value (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input (B)) c w)
    (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count (pairFst c)) (e requested : ℕ)
    (he : e ≤ 2^(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width (pairFst c))
    (hrequested : requested ≤ 2^(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width (pairFst c)) :
    IntegralMixedPhysicalTraceCutTest.value hn ht ha hR false
      (pair (pair c w) (IntegralFramedPhysicalTraceCutSource.datum
        (List.replicate (CoefficientMarkedRecordCutSource.birth (n := n) (pairFst c) k) true) e requested)) =
    InfinitesimalSign.encode (SignType.sign
      ((CoefficientMarkedRecordTraceProbePhysical.polynomial (B).parameters (B).plan (B).data
        (CoefficientMarkedRecordRowLayout.key (n := n) (pairFst c) k (BinaryNatCode.encode 2)) requested e).eval₂
        (Int.castRingHom ℝ) (CoefficientFinitePhysicalQuery.natural
          (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input (B)) c w hw).val))) := by
  let p := CoefficientMarkedRecordRawCutMetadata.parent hn ht ha hR (pairFst c) k
  let u := List.replicate (CoefficientMarkedRecordCutSource.birth (n := n) (pairFst c) k) true
  have hp : IntegralFramedPhysicalTraceCutSource.parent (B) c u = p := parent hn ht ha hR c k
  have hs : IntegralMixedVirtualTaskBits.saved (B).parameters p =
      CoefficientMarkedRecordRowLayout.key (n := n) (pairFst c) k (BinaryNatCode.encode 2) :=
    CoefficientMarkedRecordRawCutMetadata.parent_saved hn ht ha hR (pairFst c) k hk
  have hr : pairFst (IntegralMixedVirtualTaskBits.saved (B).parameters p) = pairFst ((B).key c) := by
    rw [hs, terminal hn ht ha hR c]
    simp only [CoefficientMarkedRecordRowLayout.key, CoefficientMarkedRecordRawCutMetadata.terminal,
      IntegralMixedFramedHistoryFamilyBits.keyAt, pairFst_pair]
  have hc : IntegralMixedFramedFullCutProbeBits.Active (B).parameters p :=
    CoefficientMarkedRecordRawCutMetadata.parent_active hn ht ha hR (pairFst c) k hk
  have he' : e ≤ 2^(B).parameters.width (RankedHistoryTask.root p) := by
    rw [show RankedHistoryTask.root p = pairFst c from CoefficientMarkedRecordRawCutMetadata.parent_root hn ht ha hR (pairFst c) k]
    exact he
  have hk' : requested ≤ 2^(B).parameters.width (RankedHistoryTask.root p) := by
    rw [show RankedHistoryTask.root p = pairFst c from CoefficientMarkedRecordRawCutMetadata.parent_root hn ht ha hR (pairFst c) k]
    exact hrequested
  have hf : (family (B).parameters (B).plan (B).data).birth (IntegralMixedVirtualTaskBits.saved (B).parameters p) ≤ (family (B).parameters (B).plan (B).data).birth ((B).key c) := by
    rw [terminal hn ht ha hR c]
    exact CoefficientMarkedRecordRawCutMetadata.terminal_valid hn ht ha hR (pairFst c) k hk
  have h := CoefficientMarkedRecordTraceProbeReadback.value (B)
    (IntegralMixedPhysicalTraceCutTest.key_context hn ht ha hR false)
    (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha hR false)
    (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha hR false)
    (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR false) c w u hw
    (by rw [hp]; exact hr) e requested (by rw [hp]; exact hc)
    (by rw [hp]; exact he') (by rw [hp]; exact hk') (by rw [hp]; exact hf)
  rw [hp, hs] at h
  exact h

end LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeNative
