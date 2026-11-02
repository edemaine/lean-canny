/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateValue
/-! # Native bounded-state execution of the limit-coordinate coefficient reader -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitCoordinateNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
open IntegralMixedValueCoefficientTasks (Labels labels_FP)
open IntegralMixedLimitCoordinateValue
open scoped Classical
attribute [local irreducible] IntegralMixedLimitCoordinateValue.value

def Selected (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q=4 ∧ isPhase .companion q ∧
    IntegralMixedVirtualContextBits.context P q ∧
    get P .slot8 q < IntegralMixedCoordinateCoefficientTasks.choiceBound P F q ∧
    get P .coefficient q ≤ get P .slot8 q ∧ Labels P F (IntegralMixedLimitCoordinateTasks.prepare P q)
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (Selected P F q) := inferInstanceAs (Decidable (_ ∧ _))

theorem selected_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : FPPred (Selected P F) :=
  (IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 4)).and
      ((isPhase_FP .companion).and ((IntegralMixedVirtualContextBits.context_FP P a).and
        (((get_binary P a .slot8).lt (IntegralMixedCoordinateCoefficientTasks.choiceBound_binary P a F h)).and
          (((get_binary P a .coefficient).le (get_binary P a .slot8)).and
            ((labels_FP P a F h).comp (IntegralMixedLimitCoordinateTasks.prepare_FP P a)))))))

def stateBound (P : Parameters) (q : List Bool) :=
  2*q.length+2*(birth P q+1).size+(modulus P q).size+2

theorem stateBound_unary (P : Parameters) (a : Access P) : UnaryFn (stateBound P) := by
  have HC : UnaryFn (fun q => (birth P q+1).size) :=
    (UnaryFn.length (BinaryFn.ofUnary ((IntegralMixedOldHeightBits.birth_unary P a).add (UnaryFn.const 1))).bits_mem_FP).of_eq
      (fun _ => BinaryNatCode.length_encode _)
  have HM : UnaryFn (fun q => (modulus P q).size) :=
    (UnaryFn.length (modulus_binary P a).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 2).mul HC)).add HM).add (UnaryFn.const 2)

theorem state_length_at (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (R : Routing) (answer : List Bool → List Bool) (q : List Bool) (hs : Selected P F q)
    (he : RepliesAt P F R answer q) (t : ℕ) :
    (RecursiveFold.encState (((IntegralMixedLimitCoordinateRequests.program P F R).controller.reference answer)^[t]
      ((IntegralMixedLimitCoordinateRequests.program P F R).initial q))).length ≤ stateBound P q := by
  have HL : answer (IntegralMixedLimitCoordinateRequests.task P F R (pair q (BinaryNatCode.encode (birth P q)))) =
      residueBits (oldCoefficient P F q : ZMod (modulus P q)) := by
    rw [IntegralMixedLimitCoordinateRequests.task_last]
    exact he.critical.trans (critical_value P F g q hs.1 hs.2.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2)
  have H := PoweredPrefixProductModulus.orbit_length (birth P) (IntegralMixedLimitCoordinateRequests.exponent P F)
    (IntegralMixedLimitCoordinateRequests.modulusPredecessor P) (IntegralMixedLimitCoordinateRequests.task P F R)
    answer (modulus P) (funext (IntegralMixedLimitCoordinateRequests.modulusPredecessor_value P)) q (modulus_ne_zero P q)
    (fun i => (bankScalar P F q i : ZMod (modulus P q))) (oldCoefficient P F q : ZMod (modulus P q))
    (leading_reply P F g R answer q he.bank) HL t
  simpa only [IntegralMixedLimitCoordinateRequests.program, stateBound, Turing.MultiTapeTM.encNat_apply, Nat.size_eq_bits_len] using H

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (R : Routing) (hr : RoutingAccess R) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (IntegralMixedLimitCoordinateRequests.program P F R).controller
  certificates := IntegralMixedLimitCoordinateRequests.certificates P a F h R hr
  selected q := decide (Selected P F q)
  selected_FP := (selected_FP P a F h).flag_mem_FP
  model := value P F
  clock q := birth P q+1
  clock_binary := BinaryFn.ofUnary ((IntegralMixedOldHeightBits.birth_unary P a).add (UnaryFn.const 1))
  stateBound := stateBound P
  stateBound_unary := stateBound_unary P a

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (R : Routing) (hr : RoutingAccess R)
    (answer : List Bool → List Bool) (he : ∀ q, Selected P F q → RepliesAt P F R answer q) :
    Correct (machine P a F h R hr) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (IntegralMixedLimitCoordinateRequests.program P F R).halted_after answer q
  · intro q t hq hh
    have hs : Selected P F q := of_decide_eq_true hq
    exact ((IntegralMixedLimitCoordinateRequests.program P F R).output_when_halted answer q t hh).trans
      (value_at P F g R answer q hs.1 hs.2.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2 (he q hs))
  · intro q t hq
    exact state_length_at P F g R answer q (of_decide_eq_true hq) (he q (of_decide_eq_true hq)) t
  · intro q child budget hq hc
    have hs : Selected P F q := of_decide_eq_true hq
    have HC := IntegralMixedVirtualNativeLowerBits.fold_requests_bound (IntegralMixedLimitCoordinateRequests.program P F R) answer budget q child hc
    obtain ⟨i, hi, rfl⟩ := ((IntegralMixedLimitCoordinateRequests.program P F R).requests_iff answer q child).mp HC
    exact IntegralMixedLimitCoordinateRequests.task_frame P F g R q hs.2.1 i hi

end LeanCanny.Algebra.IntegralMixedLimitCoordinateNative
