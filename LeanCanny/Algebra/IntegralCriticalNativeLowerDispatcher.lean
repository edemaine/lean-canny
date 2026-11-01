/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeOriginal
public import LeanCanny.Algebra.IntegralCriticalNativeDerivative
public import LeanCanny.Algebra.IntegralCriticalNativeHeight
public import LeanCanny.Algebra.IntegralCriticalNativeMonomial
public import LeanCanny.Algebra.IntegralCriticalNativeLowerPowers
public import LeanCanny.Algebra.IntegralCriticalNativeProductEntry
public import LeanCanny.Algebra.IntegralCriticalNativeTerm
public import LeanCanny.Algebra.IntegralCriticalNativeLowerFolds
public import LeanCanny.Algebra.IntegralCriticalNativeFrozenPower
public import LeanCanny.Algebra.IntegralCriticalNativeConstant
public import LeanCanny.Algebra.IntegralCriticalNativeFrozenLower
public import LeanCanny.Algebra.IntegralCriticalNativeCoordinateProduct
public import LeanCanny.Algebra.IntegralCriticalNativeEulerObjective
public import LeanCanny.Algebra.IntegralCriticalNativeEulerLower
/-! # One native lower dispatcher with charged original-coefficient input -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeLowerDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev Primitive (F : Scripts) := SpaceFunction (IntegralCriticalActualOriginalLeaf.rawReader F)
abbrev Matches26 (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) : Prop :=
  ∀ q, IntegralCriticalTotalCompanionBits.valid F q → isPhase .companion q → answer F x q = IntegralCriticalFlatHeightBits.companionValue F q

noncomputable def stage0 (F : Scripts) (h : Controls F) (a : Primitive F) : Machine := IntegralCriticalNativeOriginalBits.machine F h a
noncomputable def stage1 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeDerivativeBits.machine F h
noncomputable def stage2 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeHeightBits.machine F h
noncomputable def stage3 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeMonomialBits.machine F h
noncomputable def stage4 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeLowerPowerBits.factorMachine F h
noncomputable def stage5 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeProductEntryBits.machine F h
noncomputable def stage6 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeLowerPowerBits.productMachine F h
noncomputable def stage7 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeTermBits.machine F h
noncomputable def stage8 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeLowerFoldBits.gridMachine F h
noncomputable def stage9 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeFrozenPowerBits.machine F h
noncomputable def stage10 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeLowerFoldBits.frozenMachine F h
noncomputable def stage11 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeConstantBits.machine F h
noncomputable def stage12 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeFrozenLowerBits.machine F h
noncomputable def stage13 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeCoordinateProductBits.machine F h
noncomputable def stage14 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeLowerFoldBits.eulerMachine F h
noncomputable def stage15 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeEulerObjectiveBits.machine F h
noncomputable def stage16 (F : Scripts) (h : Controls F) (_a : Primitive F) : Machine := IntegralCriticalNativeEulerLowerBits.machine F h

noncomputable def inner (F : Scripts) (h : Controls F) (a : Primitive F) : Machine :=
  (stage0 F h a).choose ((stage1 F h a).choose ((stage2 F h a).choose ((stage3 F h a).choose ((stage4 F h a).choose ((stage5 F h a).choose ((stage6 F h a).choose ((stage7 F h a).choose ((stage8 F h a).choose ((stage9 F h a).choose ((stage10 F h a).choose ((stage11 F h a).choose ((stage12 F h a).choose ((stage13 F h a).choose ((stage14 F h a).choose ((stage15 F h a).choose ((stage16 F h a).choose (zero)))))))))))))))))

theorem right_selected (M N : Machine) (q : List Bool) (h : N.selected q = true) : (M.choose N).selected q = true := by
  change (M.selected q || N.selected q) = true
  rw [h, Bool.or_true]

theorem inner_selected (F : Scripts) (h : Controls F) (a : Primitive F) (q : List Bool) : (inner F h a).selected q = true := by
  unfold inner
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  rfl

theorem inner_correct (F : Scripts) (h : Controls F) (a : Primitive F)
    (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : IntegralCriticalNativeLowerBits.Matches F x) (h26 : Matches26 F x) :
    Correct (inner F h a) (answer F x) (Frame F) := by
  unfold inner
  apply choose_correct _ _ _ _ (IntegralCriticalNativeOriginalBits.correct F h a (answer F x))
  apply choose_correct _ _ _ _ (IntegralCriticalNativeDerivativeBits.correct F h x hm)
  apply choose_correct _ _ _ _ (IntegralCriticalNativeHeightBits.correct F h x h26)
  apply choose_correct _ _ _ _ (IntegralCriticalNativeMonomialBits.correct F h x hm)
  apply choose_correct _ _ _ _ (IntegralCriticalNativeLowerPowerBits.factor_correct F h x hm)
  apply choose_correct _ _ _ _ (IntegralCriticalNativeProductEntryBits.correct F h x hm)
  apply choose_correct _ _ _ _ (IntegralCriticalNativeLowerPowerBits.product_correct F h x hm)
  apply choose_correct _ _ _ _ (IntegralCriticalNativeTermBits.correct F h x hm)
  apply choose_correct _ _ _ _ (IntegralCriticalNativeLowerFoldBits.grid_correct F h x hm)
  apply choose_correct _ _ _ _ (IntegralCriticalNativeFrozenPowerBits.correct F h x hm)
  apply choose_correct _ _ _ _ (IntegralCriticalNativeLowerFoldBits.frozen_correct F h x hm)
  apply choose_correct _ _ _ _ (IntegralCriticalNativeConstantBits.correct F h x hm)
  apply choose_correct _ _ _ _ (IntegralCriticalNativeFrozenLowerBits.correct F h x hm)
  apply choose_correct _ _ _ _ (IntegralCriticalNativeCoordinateProductBits.correct F h x hm)
  apply choose_correct _ _ _ _ (IntegralCriticalNativeLowerFoldBits.euler_correct F h x hm)
  apply choose_correct _ _ _ _ (IntegralCriticalNativeEulerObjectiveBits.correct F h x hm)
  apply choose_correct _ _ _ _ (IntegralCriticalNativeEulerLowerBits.correct F h x hm)
  exact zero_correct _ _

noncomputable def machine (F : Scripts) (h : Controls F) (a : Primitive F) : Machine :=
  ((inner F h a).withGuard (fun q => decide (IntegralCriticalTotalCompanionBits.valid F q))
    (IntegralCriticalTotalCompanionBits.valid_FP F h.task).flag_mem_FP).choose zero

theorem machine_selected (F : Scripts) (h : Controls F) (a : Primitive F) (q : List Bool) : (machine F h a).selected q = true :=
  right_selected _ _ q rfl

theorem correct (F : Scripts) (h : Controls F) (a : Primitive F)
    (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : IntegralCriticalNativeLowerBits.Matches F x) (h26 : Matches26 F x) :
    Correct (machine F h a) (answer F x) (Frame F) := by
  apply choose_correct _ _ _ _ ?_ (zero_correct _ _)
  exact withGuard_correct _ _ _ _ _ (inner_correct F h a x hm h26) (fun q _ => inner_selected F h a q)

abbrev State (F : Scripts) (h : Controls F) (a : Primitive F) := (machine F h a).State
noncomputable abbrev inhabited (F : Scripts) (h : Controls F) (a : Primitive F) : Inhabited (State F h a) := ⟨(machine F h a).defaultValue⟩
noncomputable def encoding (F : Scripts) (h : Controls F) (a : Primitive F) : State F h a ↪ List Bool := (machine F h a).encoding
noncomputable def controller (F : Scripts) (h : Controls F) (a : Primitive F) := (machine F h a).controller
noncomputable def clock (F : Scripts) (h : Controls F) (a : Primitive F) := (machine F h a).clock
noncomputable def stateBound (F : Scripts) (h : Controls F) (a : Primitive F) := (machine F h a).stateBound
noncomputable def model (F : Scripts) (h : Controls F) (a : Primitive F) := (machine F h a).model

theorem certificates (F : Scripts) (h : Controls F) (a : Primitive F) :
    (controller F h a).Certificates (encQ := encBits) (encS := encoding F h a) := (machine F h a).certificates

theorem clock_binary (F : Scripts) (h : Controls F) (a : Primitive F) : BinaryFn (clock F h a) := (machine F h a).clock_binary

theorem stateBound_unary (F : Scripts) (h : Controls F) (a : Primitive F) : UnaryFn (stateBound F h a) := (machine F h a).stateBound_unary


theorem halted_after (F : Scripts) (h : Controls F) (a : Primitive F)
    (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : IntegralCriticalNativeLowerBits.Matches F x) (h26 : Matches26 F x)
    (q : List Bool) : (controller F h a).halted (((controller F h a).reference (answer F x))^[clock F h a q]
      ((controller F h a).initial q)) = true := (correct F h a x hm h26).halted q (machine_selected F h a q)

theorem output_when_halted (F : Scripts) (h : Controls F) (a : Primitive F)
    (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : IntegralCriticalNativeLowerBits.Matches F x) (h26 : Matches26 F x)
    (q : List Bool) (t : ℕ) (hh : (controller F h a).halted
      (((controller F h a).reference (answer F x))^[t] ((controller F h a).initial q)) = true) :
    (controller F h a).output (((controller F h a).reference (answer F x))^[t] ((controller F h a).initial q)) = model F h a q :=
  (correct F h a x hm h26).output q t (machine_selected F h a q) hh

theorem state_length (F : Scripts) (h : Controls F) (a : Primitive F)
    (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : IntegralCriticalNativeLowerBits.Matches F x) (h26 : Matches26 F x)
    (q : List Bool) (t : ℕ) :
    (encoding F h a (((controller F h a).reference (answer F x))^[t] ((controller F h a).initial q))).length ≤ stateBound F h a q :=
  (correct F h a x hm h26).state q t (machine_selected F h a q)

theorem requests_frame (F : Scripts) (h : Controls F) (a : Primitive F)
    (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : IntegralCriticalNativeLowerBits.Matches F x) (h26 : Matches26 F x)
    (q c : List Bool) (budget : List Bool → ℕ)
    (hc : (controller F h a).Requests (answer F x) budget q c) : Frame F q c :=
  (correct F h a x hm h26).requests q c budget (machine_selected F h a q) hc

end LeanCanny.Algebra.IntegralCriticalNativeLowerDispatcherBits
