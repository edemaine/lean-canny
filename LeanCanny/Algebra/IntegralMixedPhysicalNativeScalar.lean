/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNativeScalar
public import LeanCanny.Algebra.IntegralMixedPhysicalScalarReplyMatching
/-! # Native physical charged common-leading and original-scale scalar branches

Both routines ask original integer leading and actual common denominator
children. Their local postprocessors use modular multiplication and powering.
The original leading and denominator callbacks carry their own provenance.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalNativeScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false
inductive Kind where
  | commonLeading
  | originalScale

def code : Kind → Phase
  | .commonLeading => .monomialFactor
  | .originalScale => .productEntry

noncomputable def selected (P : Parameters) (k : Kind) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧ isPhase (code k) q ∧ get P .slot15 q = 1)

theorem selected_FP (P : Parameters) (a : Access P) (k : Kind) : (fun q => [selected P k q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 0)).and ((isPhase_FP (code k)).and ((get_binary P a .slot15).eq (BinaryFn.const 1))))).flag_mem_FP

theorem selected_iff (P : Parameters) (k : Kind) (q : List Bool) : selected P k q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧ isPhase (code k) q ∧ get P .slot15 q = 1 := by
  simp only [selected, decide_eq_true_eq]

noncomputable def program (P : Parameters) (F : Family) : Kind → RecursiveFold.Program
  | .commonLeading => IntegralMixedVirtualLeadingRequestBits.program
      (IntegralMixedPhysicalTaskBits.arithmetic P F).toGradient.toFrozen
      (IntegralMixedScalarQueryBits.originalLeading P) (IntegralMixedScalarQueryBits.commonDenominator P)
  | .originalScale => IntegralMixedVirtualScaleRequestBits.program
      (IntegralMixedPhysicalTaskBits.arithmetic P F).toGradient.toFrozen
      (IntegralMixedScalarQueryBits.originalLeading P) (IntegralMixedScalarQueryBits.commonDenominator P)
noncomputable def value (P : Parameters) (F : Family) : Kind → List Bool → List Bool
  | .commonLeading => IntegralCriticalLeadingBits.value (IntegralMixedPhysicalTaskBits.arithmetic P F).toGradient.toFrozen
  | .originalScale => IntegralMixedVirtualScaleRequestBits.value (IntegralMixedPhysicalTaskBits.arithmetic P F).toGradient.toFrozen

abbrev RepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  reply (IntegralMixedScalarQueryBits.originalLeading P q) = IntegralMixedPhysicalContextBits.originalLeadingValue P F q ∧
    reply (IntegralMixedScalarQueryBits.commonDenominator P q) = IntegralMixedPhysicalDenominatorBits.value P F q

theorem leading_reply (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool) (q : List Bool) (he : RepliesAt P F reply q) :
    reply (IntegralMixedScalarQueryBits.originalLeading P q) = (IntegralMixedPhysicalTaskBits.access P a F h).leading q :=
  he.1.trans ((IntegralMixedPhysicalTaskBits.access P a F h).leading_eq q).symm

theorem denominator_reply (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool) (q : List Bool) (he : RepliesAt P F reply q) :
    reply (IntegralMixedScalarQueryBits.commonDenominator P q) = (IntegralMixedPhysicalTaskBits.access P a F h).denominator q :=
  he.2.trans ((IntegralMixedPhysicalTaskBits.access P a F h).denominator_eq q).symm

theorem certificates (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (k : Kind) :
    (program P F k).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) := by
  cases k
  · exact IntegralMixedVirtualLeadingRequestBits.certificates _ (IntegralMixedPhysicalTaskBits.access P a F h).toEuler.toGradient.toFrozen _ _
      (IntegralMixedScalarQueryBits.scalarQuery_FP P a .originalCoefficient)
      (IntegralMixedScalarQueryBits.scalarQuery_FP P a .derivativeCoefficient)
  · exact IntegralMixedVirtualScaleRequestBits.certificates _ (IntegralMixedPhysicalTaskBits.access P a F h).toEuler.toGradient.toFrozen _ _
      (IntegralMixedScalarQueryBits.scalarQuery_FP P a .originalCoefficient)
      (IntegralMixedScalarQueryBits.scalarQuery_FP P a .derivativeCoefficient)

theorem value_at (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (k : Kind)
    (reply : List Bool → List Bool) (q : List Bool) (he : RepliesAt P F reply q) :
    (program P F k).value reply q = value P F k q := by
  cases k
  · exact IntegralMixedVirtualLeadingRequestBits.value_at _ (IntegralMixedPhysicalTaskBits.access P a F h).toEuler.toGradient.toFrozen
      _ _ reply q (leading_reply P a F h reply q he) (denominator_reply P a F h reply q he)
  · exact IntegralMixedVirtualScaleRequestBits.value_at _ (IntegralMixedPhysicalTaskBits.access P a F h).toEuler.toGradient.toFrozen
      _ _ reply q (leading_reply P a F h reply q he) (denominator_reply P a F h reply q he)

noncomputable abbrev stateBound (P : Parameters) (F : Family) :=
  IntegralMixedVirtualLeadingRequestBits.stateBound (IntegralMixedPhysicalTaskBits.arithmetic P F).toGradient.toFrozen

theorem stateBound_unary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : UnaryFn (stateBound P F) :=
  IntegralMixedVirtualLeadingRequestBits.stateBound_unary _ (IntegralMixedPhysicalTaskBits.access P a F h).toEuler.toGradient.toFrozen

theorem state_length_at (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (k : Kind)
    (reply : List Bool → List Bool) (q : List Bool) (he : RepliesAt P F reply q) (t : ℕ) :
    (RecursiveFold.encState (((program P F k).controller.reference reply)^[t] ((program P F k).initial q))).length ≤ stateBound P F q := by
  cases k
  · exact IntegralMixedVirtualLeadingRequestBits.state_length_at _ (IntegralMixedPhysicalTaskBits.access P a F h).toEuler.toGradient.toFrozen
      _ _ reply q (leading_reply P a F h reply q he) (denominator_reply P a F h reply q he) t
  · exact IntegralMixedVirtualScaleRequestBits.state_length_at _ (IntegralMixedPhysicalTaskBits.access P a F h).toEuler.toGradient.toFrozen
      _ _ reply q (leading_reply P a F h reply q he) (denominator_reply P a F h reply q he) t

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (k : Kind) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (program P F k).controller
  certificates := certificates P a F h k
  selected := selected P k
  selected_FP := selected_FP P a k
  model := value P F k
  clock := fun _ => 2
  clock_binary := BinaryFn.const 2
  stateBound := stateBound P F
  stateBound_unary := stateBound_unary P a F h

theorem requests_frame (P : Parameters) (F : Family) (k : Kind) (reply : List Bool → List Bool)
    (q c : List Bool) (budget : List Bool → ℕ) (hr : IntegralMixedRoutineTaskBits.routine P q = 0)
    (hp : isPhase (code k) q) (hc : (program P F k).controller.Requests reply budget q c) : IntegralMixedRoutineTaskBits.Frame P q c := by
  have HC := IntegralMixedPhysicalContextBits.fold_requests_bound (program P F k) reply budget q c hc
  cases k
  · rcases (IntegralMixedVirtualLeadingRequestBits.requests_iff _ _ _ reply q c).mp HC with rfl | rfl
    · exact IntegralMixedScalarQueryBits.scalar_frame_phase P .originalCoefficient q hr (by change phase q = 3 at hp; rw [hp]; decide)
    · exact IntegralMixedScalarQueryBits.scalar_frame_phase P .derivativeCoefficient q hr (by change phase q = 3 at hp; rw [hp]; decide)
  · rcases (IntegralMixedVirtualScaleRequestBits.requests_iff _ _ _ reply q c).mp HC with rfl | rfl
    · exact IntegralMixedScalarQueryBits.scalar_frame_phase P .originalCoefficient q hr (by change phase q = 5 at hp; rw [hp]; decide)
    · exact IntegralMixedScalarQueryBits.scalar_frame_phase P .derivativeCoefficient q hr (by change phase q = 5 at hp; rw [hp]; decide)

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (k : Kind)
    (reply : List Bool → List Bool) (he : ∀ q, selected P k q = true → RepliesAt P F reply q) :
    Correct (machine P a F h k) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    cases k <;> exact (program P F _).halted_after reply q
  · intro q t hq hh
    simp only [machine] at hh ⊢
    exact ((program P F k).output_when_halted reply q t hh).trans (value_at P a F h k reply q (he q hq))
  · intro q t hq
    exact state_length_at P a F h k reply q (he q hq) t
  · intro q c budget hq hc
    have HQ := (selected_iff P k q).mp hq
    exact requests_frame P F k reply q c budget HQ.2.1 HQ.2.2.1 hc

theorem machine_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (k : Kind) :
    (machine P a F h k).model = value P F k := rfl

theorem machine_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (k : Kind) :
    (machine P a F h k).selected = selected P k := rfl

theorem value_canonical (P : Parameters) (F : Family) (k : Kind) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = value P F k q := by
  cases k <;> exact ⟨_, rfl⟩
end LeanCanny.Algebra.IntegralMixedPhysicalNativeScalarBits
