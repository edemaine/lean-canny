/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeUpperPowers
/-! # One concrete native dispatcher for critical-history phases seventeen to twenty-six

Invalid births and reserved phase twenty use zero. Finite-axis guards keep
raw reduction, action and factor entries outside their matrices local.
The semantic contracts assume only the stated actual component values.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable def inner (F : Scripts) (h : Controls F) : Machine :=
  (stage17 F h).choose ((stage18 F h).choose ((stage19 F h).choose ((stage21 F h).choose
    ((stage22 F h).choose ((stage23 F h).choose ((stage24 F h).choose ((stage25 F h).choose
      ((stage26 F h).choose zero))))))))

theorem right_selected (M N : Machine) (q : List Bool) (h : N.selected q = true) : (M.choose N).selected q = true := by
  change (M.selected q || N.selected q) = true
  rw [h, Bool.or_true]

theorem inner_selected (F : Scripts) (h : Controls F) (q : List Bool) : (inner F h).selected q = true := by
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
  rfl

theorem inner_correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hx : Matches F x) : Correct (inner F h) (answer F x) (Frame F) := by
  unfold inner
  apply choose_correct _ _ _ _ (correct17 F h x hx)
  apply choose_correct _ _ _ _ (correct18 F h x hx)
  apply choose_correct _ _ _ _ (correct19 F h x hx)
  apply choose_correct _ _ _ _ (correct21 F h x hx)
  apply choose_correct _ _ _ _ (correct22 F h x hx)
  apply choose_correct _ _ _ _ (correct23 F h x hx)
  apply choose_correct _ _ _ _ (correct24 F h x hx)
  apply choose_correct _ _ _ _ (correct25 F h x hx)
  apply choose_correct _ _ _ _ (correct26 F h x hx)
  exact zero_correct _ _

noncomputable def machine (F : Scripts) (h : Controls F) : Machine :=
  ((inner F h).withGuard (fun q => decide (IntegralCriticalTotalCompanionBits.valid F q))
    (IntegralCriticalTotalCompanionBits.valid_FP F h.task).flag_mem_FP).choose zero

theorem machine_selected (F : Scripts) (h : Controls F) (q : List Bool) : (machine F h).selected q = true :=
  right_selected _ _ q rfl

theorem correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hx : Matches F x) : Correct (machine F h) (answer F x) (Frame F) := by
  apply choose_correct _ _ _ _ ?_ (zero_correct _ _)
  exact withGuard_correct _ _ _ _ _ (inner_correct F h x hx) (fun q _ => inner_selected F h q)

abbrev State (F : Scripts) (h : Controls F) := (machine F h).State
noncomputable abbrev inhabited (F : Scripts) (h : Controls F) : Inhabited (State F h) := ⟨(machine F h).defaultValue⟩
noncomputable def encoding (F : Scripts) (h : Controls F) : State F h ↪ List Bool := (machine F h).encoding
noncomputable def controller (F : Scripts) (h : Controls F) := (machine F h).controller
noncomputable def clock (F : Scripts) (h : Controls F) := (machine F h).clock
noncomputable def stateBound (F : Scripts) (h : Controls F) := (machine F h).stateBound
noncomputable def model (F : Scripts) (h : Controls F) := (machine F h).model

theorem certificates (F : Scripts) (h : Controls F) :
    (controller F h).Certificates (encQ := encBits) (encS := encoding F h) := (machine F h).certificates
theorem clock_binary (F : Scripts) (h : Controls F) : BinaryFn (clock F h) := (machine F h).clock_binary
theorem stateBound_unary (F : Scripts) (h : Controls F) : UnaryFn (stateBound F h) := (machine F h).stateBound_unary

theorem halted_after (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hx : Matches F x) (q : List Bool) :
    (controller F h).halted (((controller F h).reference (answer F x))^[clock F h q] ((controller F h).initial q)) = true :=
  (correct F h x hx).halted q (machine_selected F h q)

theorem output_when_halted (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hx : Matches F x) (q : List Bool) (t : ℕ)
    (hh : (controller F h).halted (((controller F h).reference (answer F x))^[t] ((controller F h).initial q)) = true) :
    (controller F h).output (((controller F h).reference (answer F x))^[t] ((controller F h).initial q)) = model F h q :=
  (correct F h x hx).output q t (machine_selected F h q) hh

theorem state_length (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hx : Matches F x) (q : List Bool) (t : ℕ) :
    (encoding F h (((controller F h).reference (answer F x))^[t] ((controller F h).initial q))).length ≤ stateBound F h q :=
  (correct F h x hx).state q t (machine_selected F h q)

theorem requests_frame (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hx : Matches F x) (q c : List Bool) (budget : List Bool → ℕ)
    (hc : (controller F h).Requests (answer F x) budget q c) : Frame F q c :=
  (correct F h x hx).requests q c budget (machine_selected F h q) hc

end LeanCanny.Algebra.IntegralCriticalNativeUpperBits
