/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCurrentQSquareSpace
public import LeanCanny.Algebra.IntegralMixedFramedChoiceProbeBounds
public import LeanCanny.Algebra.IntegralMixedCutCoefficientQuery
/-! # Native complete successor sampling for selected-cut tests

Every task, including a malformed one, gets a positive bounded prefix.
At an active parent the prefix has exactly one additional scalar. Test
indices leave this source key and its joint root ordinal unchanged.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutSuccessor
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical

def key (P : Parameters) (c : List Bool) := IntegralMixedFramedHistoryFamilyBits.keyAt
  (RankedHistoryTask.root c) (birth P c+1) (BinaryNatCode.encode (get P .slot15 c))
theorem key_FP (P : Parameters) (a : Access P) : key P∈FP :=
  mem_FP_pair RankedHistoryTask.root_FP (mem_FP_pair
    ((BinaryFn.ofUnary (IntegralMixedOldHeightBits.birth_unary P a)).add (BinaryFn.const 1)).bits_mem_FP
    (get_binary P a .slot15).bits_mem_FP)

theorem prefix_length (P : Parameters) (c : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.prefixLength P (key P c)=min (birth P c+1) (P.cap (RankedHistoryTask.root c)+1) := by
  simp only [IntegralMixedFramedHistoryFamilyBits.prefixLength,IntegralMixedFullHistoryFamilyBits.prefixLength,
    key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem positive (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :
    0<(family P D H).birth (key P c) := by
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth,prefix_length]
  exact lt_min (Nat.succ_pos _) (Nat.succ_pos _)

theorem active_count (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P c) :
    (family P D H).birth (key P c)=birth P c+1 := by
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth,prefix_length,min_eq_left]
  have hb:=ha.1
  unfold IntegralMixedVirtualCaps.valid at hb
  omega

noncomputable abbrev input (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) :=
  IntegralFramedCompleteSquare.input P D H L F C hs (key P) (positive P D H)

theorem access (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew c)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : (input P D H L F C hs).Access :=
  IntegralFramedCurrentQSquare.access_native P a D H Hnew c hb L F C hs hL hF hC (key P) (key_FP P a) (positive P D H)

theorem probe_arity (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (z : List Bool)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P (pairFst z)) :
    (IntegralMixedFramedChoiceProbeSourceBits.source P D H).arity (IntegralMixedCutCoefficientQueryBits.query P z)+1=
      (input P D H L F C hs).count (pairFst z) := by
  rw [IntegralMixedFramedChoiceProbeSourceBits.arity,IntegralMixedCutCoefficientQueryBits.query_birth]
  exact (active_count P D H (pairFst z) ha).symm

end LeanCanny.Encoding.IntegralFramedCutSuccessor
