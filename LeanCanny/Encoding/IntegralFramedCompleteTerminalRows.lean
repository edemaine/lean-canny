/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCompleteSquare
public import LeanCanny.Algebra.IntegralMixedFramedFamilyTerminalRows

/-! # Complete-input row transport at the default-extended terminal key -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCompleteSquare
open LeanCanny.Algebra IntegralCriticalHistoryTask IntegralMixedFramedStepHeight
open IntegralMixedFramedHistoryScript

private theorem family_rows_congr (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q q' : List Bool) (he : q=q') :
    HEq (((IntegralMixedFramedHistoryFamilyBits.family P D H).state q).sampler.scalarPrefix.rows)
      (((IntegralMixedFramedHistoryFamilyBits.family P D H).state q').sampler.scalarPrefix.rows) := by
  cases he
  rfl

theorem rows_after_script (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool→ℕ)
    (h : FamilyInputs P D L F C) (key : List Bool→List Bool)
    (hpos : ∀ u,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key u))
    (u root : List Bool) (m : ℕ) (hm : m≤P.cap root) (hlen : (D.rules root).length=m)
    (hkey : key u=IntegralMixedFramedHistoryFamilyBits.keyAt root (m+1) []) :
    HEq ((input P D H L F C h key hpos).system u)
      (run (IntegralMixedFramedHistoryFamilyBits.initial P D root)
        (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root::D.rules root)
        (by simp only [List.length_cons]; omega)).sampler.scalarPrefix.rows := by
  have HK : key u=IntegralMixedFramedHistoryFamilyBits.keyAt root ((D.rules root).length+1) [] :=
    hkey.trans (congrArg (fun k=>IntegralMixedFramedHistoryFamilyBits.keyAt root (k+1) []) hlen.symm)
  exact (rows_heq P D H L F C h key hpos u).trans
    ((family_rows_congr P D H _ _ HK).trans
      (IntegralMixedFramedFamilyRunView.family_terminal_rows P D H root [] (hlen.le.trans hm)))

end LeanCanny.Encoding.IntegralFramedCompleteSquare
