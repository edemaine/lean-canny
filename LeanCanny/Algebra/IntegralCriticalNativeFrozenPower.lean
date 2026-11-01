/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeLowerFrames
/-! # Native actual frozen retained-height power branch -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeFrozenPowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits IntegralCriticalNativeLowerBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap IntegralCriticalHistoryTask.rank
noncomputable abbrev source (F : Scripts) := IntegralCriticalTotalCreatingBits.FrozenStages.source F
noncomputable abbrev access (F : Scripts) (h : Controls F) := IntegralCriticalTotalCreatingBits.FrozenStages.access F h

theorem replies (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    IntegralCriticalFlatFrozenTermBits.RepliesAt F.toParameters (source F) (answer F x) q := by
  intro _ r t
  exact (matches_matrix F x hm .clearedHeight (by decide)
    (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
    (by simpa only [pairFst_pair] using hv)).trans (IntegralCriticalActualFrozenTransport.power_height_child F q r t)

noncomputable def machine (F : Scripts) (h : Controls F) : Machine where
  State := RecursiveController.Controller.ChoiceState SingleCall.State (List Bool)
  defaultValue := (false, default, [])
  encoding := RecursiveController.Controller.encChoice SingleCall.encState Turing.MultiTapeTM.encBits
  controller := IntegralCriticalFlatFrozenTermBits.controller F.toParameters (source F) (access F h)
  certificates := IntegralCriticalTotalCreatingBits.FrozenStages.term_certificates F h
  selected := selected F .frozenPowerTerm
  selected_FP := selected_FP F h .frozenPowerTerm
  model := IntegralCriticalActualScalarModels.frozenTerm F
  clock := IntegralCriticalFlatFrozenTermBits.clock F.toParameters (source F)
  clock_binary := IntegralCriticalTotalCreatingBits.FrozenStages.term_clock_binary F h
  stateBound := IntegralCriticalFlatFrozenTermBits.stateBound F.toParameters (source F)
  stateBound_unary := IntegralCriticalTotalCreatingBits.FrozenStages.term_stateBound_unary F h

theorem correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x) :
    Correct (machine F h) (answer F x) (Frame F) := by
  constructor
  · intro q hq
    exact IntegralCriticalFlatFrozenTermBits.halted_after_local F.toParameters (source F) (access F h) (answer F x) q
      (replies F x hm q ((selected_iff F .frozenPowerTerm q).mp hq).1)
  · intro q t hq hh
    exact (IntegralCriticalFlatFrozenTermBits.value_local F.toParameters (source F) (access F h) (answer F x) q
      (replies F x hm q ((selected_iff F .frozenPowerTerm q).mp hq).1) t hh).trans
        (IntegralCriticalActualScalarModels.frozenTerm_eq F q).symm
  · intro q t hq
    exact IntegralCriticalFlatFrozenTermBits.state_length_local F.toParameters (source F) (access F h) (answer F x) q
      (replies F x hm q ((selected_iff F .frozenPowerTerm q).mp hq).1) t
  · intro q c budget hq hc
    have HP := ((selected_iff F .frozenPowerTerm q).mp hq).2
    change phase q = 9 at HP
    obtain ⟨r, t, rfl⟩ := IntegralCriticalFlatFrozenTermBits.requests_in_bounds_local F.toParameters (source F) (access F h)
      (answer F x) q (replies F x hm q ((selected_iff F .frozenPowerTerm q).mp hq).1) budget c hc
    simpa only [pairFst_pair] using frame_matrix F .clearedHeight
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))) (by
        simp only [pairFst_pair]
        change 2 < phase q
        omega)

end LeanCanny.Algebra.IntegralCriticalNativeFrozenPowerBits
