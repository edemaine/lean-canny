/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeLowerContracts
/-! # Native phase twelve from the actual cleared coefficient and frozen constant -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeFrozenLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits IntegralCriticalNativeLowerBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily IntegralCriticalHistoryTask.get
  IntegralCriticalHistoryTask.numericCap IntegralCriticalHistoryTask.rank

noncomputable abbrev source (F : Scripts) := IntegralCriticalTotalCreatingBits.FrozenStages.source F

noncomputable def machine (F : Scripts) (h : Controls F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (IntegralCriticalFlatFrozenLowerBits.program F.toParameters (source F)).controller
  certificates := IntegralCriticalFlatFrozenLowerBits.certificates F.toParameters h.task.toAccess (source F)
    (IntegralCriticalTotalCreatingBits.FrozenStages.access F h)
  selected := selected F .frozenLower
  selected_FP := selected_FP F h .frozenLower
  model := IntegralCriticalActualScalarModels.frozenLower F
  clock := fun _ => 2
  clock_binary := BinaryFn.const 2
  stateBound := IntegralCriticalFlatFrozenLowerBits.stateBound (source F)
  stateBound_unary := IntegralCriticalFlatFrozenLowerBits.stateBound_unary (source F)
    (IntegralCriticalTotalCreatingBits.FrozenStages.access F h)

theorem cleared_reply (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    answer F x (IntegralCriticalFlatFrozenLowerBits.clearedTask F.toParameters (source F) q) = (source F).toSource.value q := by
  exact (matches_spatial F x hm .clearedGridSum (by decide) 0
    (pair q (pair (BinaryNatCode.encode (get F.toParameters .derivative q)) (BinaryNatCode.encode ((source F).target q))))
    (by simpa only [pairFst_pair] using hv)).trans (IntegralCriticalActualSpatialTransport.frozenLower_cleared_child F q)

theorem constant_reply (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    answer F x (IntegralCriticalFlatEulerBits.next F.toParameters .frozenConstant q) = (source F).constantValue q :=
  (matches_next F x hm .frozenConstant (by decide) q hv).trans (IntegralCriticalActualScalarModels.frozenLower_constant_child F q)

theorem correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hm : Matches F x) : Correct (machine F h) (answer F x) (Frame F) := by
  constructor
  · intro q _
    exact IntegralCriticalFlatFrozenLowerBits.halted_after F.toParameters (source F) (answer F x) q
  · intro q t hq hh
    exact (IntegralCriticalFlatFrozenLowerBits.output_when_halted_local F.toParameters (source F) (answer F x) q
      (cleared_reply F x hm q ((selected_iff F .frozenLower q).mp hq).1)
      (constant_reply F x hm q ((selected_iff F .frozenLower q).mp hq).1) t hh).trans
        (IntegralCriticalActualScalarModels.frozenLower_eq F q).symm
  · intro q t hq
    exact IntegralCriticalFlatFrozenLowerBits.state_length_local F.toParameters (source F) (answer F x) q
      (cleared_reply F x hm q ((selected_iff F .frozenLower q).mp hq).1)
      (constant_reply F x hm q ((selected_iff F .frozenLower q).mp hq).1) t
  · intro q c budget hq hc
    have HP := ((selected_iff F .frozenLower q).mp hq).2
    change phase q = 12 at HP
    have HC := fold_requests_bound (IntegralCriticalFlatFrozenLowerBits.program F.toParameters (source F)) (answer F x) budget q c hc
    rcases (IntegralCriticalFlatFrozenLowerBits.requests_iff F.toParameters (source F) (answer F x) q c).mp HC with rfl | rfl
    · simpa only [IntegralCriticalFlatFrozenLowerBits.clearedTask, pairFst_pair] using frame_spatial F .clearedGridSum 0
        (pair q (pair (BinaryNatCode.encode (get F.toParameters .derivative q)) (BinaryNatCode.encode ((source F).target q)))) (by
          simp only [pairFst_pair]
          change 8 < phase q
          omega)
    · exact frame_next F .frozenConstant q (by change 11 < phase q; omega)

end LeanCanny.Algebra.IntegralCriticalNativeFrozenLowerBits
