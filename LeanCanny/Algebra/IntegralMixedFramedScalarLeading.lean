/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedScalarModel
public import LeanCanny.Algebra.IntegralMixedPhysicalScalarMatches
public import LeanCanny.Algebra.IntegralMixedVirtualContextScalarMatches
public import LeanCanny.Computation.NativeSingleCallBranch
/-! # The original spatial integer leading is a shared immutable scalar leaf -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedScalarLeadingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def value (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (_H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  IntegralMixedFramedScalarCellsBits.leadingValue P D q
abbrev Primitive (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) := SpaceFunction (value P D H)

attribute [local irreducible] value

noncomputable def program (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) : SingleCall.Program where
  request _ := false
  query := id
  immediate := value P D H
  finish := id

theorem certificates (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Primitive P D H) :
    (program P D H).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  (program P D H).certificates_of_space (constFn_mem_FP [false]) id_mem_FP h.computable (SpaceFunction.ofFP _ id_mem_FP).computable

noncomputable def selected (P : Parameters) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧ isPhase .originalCoefficient q ∧
    1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4)

theorem selected_iff (P : Parameters) (q : List Bool) : selected P q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧ isPhase .originalCoefficient q ∧
      1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := by simp only [selected, decide_eq_true_eq]

theorem selected_FP (P : Parameters) (a : Access P) : (fun q => [selected P q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 0)).and
      ((isPhase_FP .originalCoefficient).and (((BinaryFn.const 1).le (get_binary P a .slot15)).and ((get_binary P a .slot15).le (BinaryFn.const 4)))))).flag_mem_FP

noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Primitive P D H) : Machine :=
  ofSingleCall (program P D H) (certificates P D H h) (selected P) (selected_FP P a) (value P D H) (fun _ => 0) (UnaryFn.const 0)

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Primitive P D H) (answer : List Bool → List Bool) :
    Correct (machine P a D H h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q _; rfl
  · intro q _ hn; cases hn
  · intro q c budget _ hc
    obtain ⟨hr, _⟩ := ((program P D H).requests_iff answer budget q c).mp hc
    cases hr

theorem physical_value (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    value P D H q = IntegralMixedPhysicalContextBits.originalLeadingValue P (IntegralMixedFramedScalarCellsBits.physicalFamily P D H) q := by
  unfold value
  rfl

theorem virtual_value (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    value P D H q = IntegralMixedVirtualContextBits.originalLeadingValue P (IntegralMixedFramedScalarCellsBits.virtualFamily P D H) q := by
  unfold value
  rfl

theorem canonical (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = value P D H q := by
  unfold value IntegralMixedFramedScalarCellsBits.leadingValue
  exact ⟨_, rfl⟩

end LeanCanny.Algebra.IntegralMixedFramedScalarLeadingBits
