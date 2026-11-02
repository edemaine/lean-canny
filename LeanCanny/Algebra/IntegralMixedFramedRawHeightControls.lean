/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRawHeight
/-! # Binary controls for the source-framed raw and top matrix ceilings

The original root ceiling is independent of the Parameters.height field. It
can therefore supply that field without referring to itself. Only original
count/degree/width controls and the separate affine-node and causal schedules
are needed; neither bank nor matrix evaluation enters these controls.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRawHeight
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedStepHeight IntegralMixedFramedOriginalBounds

theorem rootRank_binary (P : Parameters) (a : Access P) : BinaryFn (rootRank P) :=
  IntegralMixedFullScriptHeight.rank_binary (a.cap.add (UnaryFn.const 1)) a.width

theorem rootFactor_binary (P : Parameters) (a : Access P) {L : List Bool → ℕ} (hL : BinaryFn L) :
    BinaryFn (rootFactor P L) :=
  IntegralMixedCutHeightProfile.factor_binary a.ambient (rootRank_binary P a) a.sourceWidth a.degree
    (BinaryFn.ofUnary (a.cap.add (UnaryFn.const 1))) hL

theorem localHeight_binary (P : Parameters) (a : Access P) {L F C : List Bool → ℕ}
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : BinaryFn (localHeight P L F C) := by
  have HR : BinaryFn (fun key => rootFactor P L (pairFst key)) := (rootFactor_binary P a hL).comp pairFst_mem_FP
  have HF : BinaryFn (fun key => F (pairFst key)) := hF.comp pairFst_mem_FP
  exact HR.mul ((HF.add (BinaryFn.const 2)).mul (familyHeight_binary P a hL hF hC))

theorem rootCeiling_binary (P : Parameters) (a : Access P) {L F C : List Bool → ℕ}
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : BinaryFn (rootCeiling P L F C) :=
  (rootFactor_binary P a hL).mul ((hF.add (BinaryFn.const 2)).mul
    (height_binary a.ambient (a.cap.add (UnaryFn.const 1)) a.width a.sourceWidth a.degree hL hF hC
      (a.cap.add (UnaryFn.const 1))))

theorem rootCeiling_update_height (P : Parameters) (L F C : List Bool → ℕ)
    (newHeight : List Bool → ℕ) (root : List Bool) :
    rootCeiling {P with height:=newHeight} L F C root=rootCeiling P L F C root := rfl

theorem rawBounds_height_binary (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ)
    (h : FamilyInputs P D L F C) (hF : ∀ root, 1≤F root)
    (hfallback : ∀ key, FallbackBounds P D H L C key)
    (hLnative : BinaryFn L) (hFnative : BinaryFn F) (hCnative : BinaryFn C) :
    BinaryFn (rawBounds P D H L F C h hF hfallback).height :=
  (rootCeiling_binary P a hLnative hFnative hCnative).comp pairFst_mem_FP

end LeanCanny.Algebra.IntegralMixedFramedRawHeight
