/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightCurrentReplies
public import LeanCanny.Algebra.IntegralMixedPhysicalScalarMatches
public import LeanCanny.Algebra.IntegralMixedVirtualContextScalarMatches
public import LeanCanny.Computation.NativeSingleCallBranch
/-! # The original spatial integer leading is a shared immutable scalar leaf -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullScalarLeadingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :=
  residueBits ((D.spatial (RankedHistoryTask.root q)).leading : ZMod (modulus P q))
abbrev Primitive (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) := SpaceFunction (value P D)

noncomputable def program (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) : SingleCall.Program where
  request _ := false
  query := id
  immediate := value P D
  finish := id

theorem certificates (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Primitive P D) :
    (program P D).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  (program P D).certificates_of_space (constFn_mem_FP [false]) id_mem_FP h.computable (SpaceFunction.ofFP _ id_mem_FP).computable

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

noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Primitive P D) : Machine :=
  ofSingleCall (program P D) (certificates P D h) (selected P) (selected_FP P a) (value P D) (fun _ => 0) (UnaryFn.const 0)

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Primitive P D) (answer : List Bool → List Bool) :
    Correct (machine P a D h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q _; rfl
  · intro q _ hn; cases hn
  · intro q c budget _ hc
    obtain ⟨hr, _⟩ := ((program P D).requests_iff answer budget q c).mp hc
    cases hr

theorem physical_value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    value P D q = IntegralMixedPhysicalContextBits.originalLeadingValue P (IntegralMixedHeightCellsBits.physicalFamily P D) q := by
  have HL : (IntegralMixedPhysicalNativeLowerBits.source P (IntegralMixedHeightCellsBits.physicalFamily P D)).leading q =
      (D.spatial (RankedHistoryTask.root q)).leading := by
    change (D.spatial (pairFst (IntegralMixedPhysicalTaskBits.saved P q))).leading = _
    exact congrArg (fun r => (D.spatial r).leading) (pairFst_pair _ _)
  unfold value IntegralMixedPhysicalContextBits.originalLeadingValue
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) HL.symm

theorem virtual_value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    value P D q = IntegralMixedVirtualContextBits.originalLeadingValue P (IntegralMixedOldHeightBits.bankFamily P D) q := by
  have HL : (IntegralMixedVirtualNativeLowerBits.source P (IntegralMixedOldHeightBits.bankFamily P D)).leading q =
      (D.spatial (RankedHistoryTask.root q)).leading := by
    change (D.spatial (pairFst (IntegralMixedVirtualTaskBits.saved P q))).leading = _
    exact congrArg (fun r => (D.spatial r).leading) (pairFst_pair _ _)
  unfold value IntegralMixedVirtualContextBits.originalLeadingValue
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) HL.symm

theorem canonical (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = value P D q := ⟨_, rfl⟩

end LeanCanny.Algebra.IntegralMixedFullScalarLeadingBits
