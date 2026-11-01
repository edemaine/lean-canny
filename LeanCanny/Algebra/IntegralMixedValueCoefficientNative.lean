/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueCoefficientValue
/-! # Native value-coefficient requests charge only the first-digit value stage

The phase-26 kernel returns the literal untruncated value-factor coefficient.
Its actual truncation and selected-kind source equality are separate explicit
identities; the kernel supplies neither an assumed coefficient evaluator nor
an assumed leading reader.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueCoefficientNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedValueCoefficientTasks
open IntegralMixedValueCoefficientValue
open scoped Classical
attribute [local irreducible] IntegralMixedValueFactorValue.value IntegralMixedValueCoefficientValue.value

noncomputable def program (P : Parameters) (F : Family) : SingleCall.Program where
  request q := decide (Labels P F q)
  query := query P F
  immediate _ := []
  finish := pairSnd
theorem controls (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : (program P F).Controls :=
  ⟨(labels_FP P a F h).flag_mem_FP, query_FP P a F h, constFn_mem_FP [], pairSnd_mem_FP⟩

abbrev RepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  Labels P F q → answer (query P F q) = IntegralMixedValueFactorValue.value P F (query P F q)

theorem value_at (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (he : RepliesAt P F answer q) : (program P F).value answer q = value P F q := by
  by_cases hk : Labels P F q
  · simp only [SingleCall.Program.value, program, hk, decide_true, ite_true, pairSnd_pair]
    exact (he hk).trans (child_value P F g q hv hk)
  · simp only [SingleCall.Program.value, program, hk, decide_false, Bool.false_eq_true, ite_false]
    exact (value_outside P F q hk).symm

def Selected (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 4 ∧ isPhase .companion q ∧
    get P .slot8 q < IntegralMixedValueTrailing.ChoiceBound
      ((IntegralMixedVirtualTaskBits.family P F).spatial q) ((IntegralMixedVirtualTaskBits.family P F).rule q)
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (Selected P F q) := inferInstanceAs (Decidable (_ ∧ _))

theorem selected_FP (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) : FPPred (Selected P F) :=
  (IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 4)).and
      ((isPhase_FP .companion).and ((get_binary P a .slot8).lt
        ((IntegralMixedValueDeterminantMetadata.dimension_binary _ _ (IntegralMixedVirtualTaskBits.metadata P a F h)).add (BinaryFn.const 2)))))

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := SingleCall.State
  defaultValue := default
  encoding := SingleCall.encState
  controller := (program P F).controller
  certificates := (program P F).certificates (controls P a F h)
  selected q := decide (Selected P F q)
  selected_FP := (selected_FP P a F h).flag_mem_FP
  model := value P F
  clock _ := 1
  clock_binary := BinaryFn.const 1
  stateBound := IntegralMixedValueHomogeneousRequest.stateBound P
  stateBound_unary := IntegralMixedValueHomogeneousRequest.stateBound_unary P a

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool)
    (he : ∀ q, Selected P F q → RepliesAt P F answer q) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (program P F).halted_after answer q
  · intro q t hq hh
    have HS : Selected P F q := of_decide_eq_true hq
    exact ((program P F).output_when_halted answer q t hh).trans (value_at P F g answer q HS.1 (he q HS))
  · intro q t hq
    have HS : Selected P F q := of_decide_eq_true hq
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    apply (program P F).state_length_of_bound answer q t ((modulus P q).size)
    intro hp
    have hk : Labels P F q := of_decide_eq_true hp
    change (answer (query P F q)).length ≤ _
    rw [he q HS hk, child_value P F g q HS.1 hk]
    exact value_length P F q
  · intro q c budget hq hc
    have HS : Selected P F q := of_decide_eq_true hq
    have HQ := (SingleCall.Program.requests_iff (program P F) answer budget q c).mp hc
    rw [HQ.2]
    exact query_frame P F q HS.2.1 HS.2.2.1

end LeanCanny.Algebra.IntegralMixedValueCoefficientNative
