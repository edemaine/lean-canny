/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutFiniteGuards
/-! # The native guard scans one complete successor point

Every coefficient test in the finite scan evaluates on the same joint
root. This theorem identifies the native predicate with exact canonical
polynomial evaluations, including the newest-coordinate padding guard.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutFiniteGuards
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



omit a hL hF hC h hb in
theorem coefficient_zero_iff (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCutSuccessor.input P D H L F C hs) c w) (e k : ℕ) :
    FiniteCoefficientSignScan.Zero (IntegralFramedCutCoefficientTest.value P D H L F C hs hFpos hf) (pair c w) e k ↔
      (IntegralFramedCutCoefficientTest.polynomial P D H L F C hs c
        (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k))).eval₂ (Int.castRingHom ℝ)
          (SquareSampleCompleteVertices.candidate (IntegralFramedCutSuccessor.input P D H L F C hs) c w hv).val=0 := by
  unfold FiniteCoefficientSignScan.Zero FiniteCoefficientSignScan.query IntegralFramedCutCoefficientTest.value
  rw [SquareSampleCompleteIndexedPolynomialTest.packet _ _ c w _ hv]
  exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff

omit a hL hF hC h hb hFpos hf in
theorem head_zero_iff (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCutSuccessor.input P D H L F C hs) c w) :
    head P D H L F C hs (pair c w)=InfinitesimalSign.encode 0 ↔
      (SquareSampleCompleteVertices.candidate (IntegralFramedCutSuccessor.input P D H L F C hs) c w hv).val
        ⟨0,IntegralFramedCutSuccessor.positive P D H c⟩=0 := by
  rw [head_packet P D H L F C hs c w hv]
  exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff

end LeanCanny.Encoding.IntegralFramedCutFiniteGuards
