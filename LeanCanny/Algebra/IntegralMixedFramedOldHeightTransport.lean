/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightBankSnapshot
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackData
public import LeanCanny.Algebra.IntegralMixedFramedNormalizationPlanning
/-! # Modulus-root and budget changes preserve actual old cleared matrices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOldHeightBankBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem rootEntry_pullback (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool→List Bool) (extra : List Bool→ℕ) (root : List Bool) (b i r t : ℕ) :
    rootEntry (IntegralMixedFramedRootPullback.parameters P project extra)
      (IntegralMixedFramedRootPullback.plan P D project extra)
      (IntegralMixedFramedRootPullback.data P D H project extra) root b i r t=
        rootEntry P D H (project root) b i r t := rfl

theorem rootEntry_planned (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (root : List Bool) (b i r t : ℕ) :
    rootEntry (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) root b i r t=
        rootEntry P D H root b i r t := rfl

theorem sourceEntry_pullback (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool→List Bool) (extra : List Bool→ℕ) (key : List Bool) (i r t : ℕ) :
    sourceEntry (IntegralMixedFramedRootPullback.parameters P project extra)
      (IntegralMixedFramedRootPullback.plan P D project extra)
      (IntegralMixedFramedRootPullback.data P D H project extra) key i r t=
        sourceEntry P D H (IntegralMixedFramedRootPullback.key project key) i r t := by
  rw [sourceEntry_root,sourceEntry_root,rootEntry_pullback,
    IntegralMixedFramedRootPullback.key_root,IntegralMixedFramedRootPullback.key_prefix]

theorem sourceEntry_planned (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (key : List Bool) (i r t : ℕ) :
    sourceEntry (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key i r t=
        sourceEntry P D H key i r t := by
  rw [sourceEntry_root,sourceEntry_root,rootEntry_planned]
  rfl

end LeanCanny.Algebra.IntegralMixedFramedOldHeightBankBits
