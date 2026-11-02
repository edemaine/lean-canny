/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullScalarUnitControls
public import LeanCanny.Algebra.IntegralMixedFramedNativeCurrentQHeight
/-! # Full scalar machines restore current-Q slopes after charged replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev physicalFamily (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) := IntegralMixedFramedScalarCellsBits.physicalFamily P D J
noncomputable abbrev virtualFamily (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) := IntegralMixedFramedOldHeightBits.bankFamily P D J

structure Controls (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) where
  tables : IntegralMixedHeaderTablesBits.Tables
  native : IntegralMixedHeaderTablesBits.Access tables
  represents : IntegralMixedFramedHeaderBits.Represents P D J tables
  leading : IntegralMixedFramedScalarLeadingBits.Primitive P D J
  physicalScales : IntegralMixedPhysicalNativeDenominatorBits.Primitive P (physicalFamily P D J)
  virtualScales : IntegralMixedVirtualContextDenominatorBits.Primitive P (virtualFamily P D J)
  height : IntegralMixedFramedCurrentQHeightBits.Controls P D J

theorem physicalInput (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :
    IntegralMixedPhysicalQueryBits.InputMetadata (physicalFamily P D J) :=
  IntegralMixedFramedPhysicalBits.inputMetadata P a D J h.tables h.native h.represents

theorem virtualInput (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :
    IntegralMixedVirtualQueryBits.InputMetadata (virtualFamily P D J) :=
  IntegralMixedFramedPhysicalBits.virtualInputMetadata P a D J h.tables h.native h.represents

theorem routingAccess (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :
    IntegralMixedOldBankCofactorBits.RoutingAccess (IntegralMixedFramedHeaderBits.routing P D) :=
  IntegralMixedFramedHeaderBits.routingAccess P a D J h.tables h.native h.represents

noncomputable def selected (P : Parameters) (p : Phase) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧ isPhase p q ∧
    1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4)
theorem selected_iff (P : Parameters) (p : Phase) (q : List Bool) : selected P p q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧ isPhase p q ∧
      1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := by simp only [selected, decide_eq_true_eq]
theorem selected_FP (P : Parameters) (a : Access P) (p : Phase) : (fun q => [selected P p q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 0)).and
      ((isPhase_FP p).and (((BinaryFn.const 1).le (get_binary P a .slot15)).and ((get_binary P a .slot15).le (BinaryFn.const 4)))))).flag_mem_FP

noncomputable def physicalDenominator (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  IntegralMixedPhysicalNativeDenominatorBits.machine P a (physicalFamily P D J) (physicalInput P a D J h)
    (IntegralMixedFramedPhysicalBits.geometry P D J)
    (IntegralMixedFramedHeaderBits.routing P D) (routingAccess P a D J h) h.physicalScales
noncomputable def virtualDenominator (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  IntegralMixedVirtualContextDenominatorBits.machine P a (virtualFamily P D J) (virtualInput P a D J h)
    (IntegralMixedFramedHistoryFamilyBits.geometry P D J) (IntegralMixedFramedHeaderBits.routing P D)
    (routingAccess P a D J h) h.virtualScales
noncomputable def denominator (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  (physicalDenominator P a D J h).choose (virtualDenominator P a D J h)

abbrev Kind := IntegralMixedPhysicalNativeScalarBits.Kind
def virtualKind : Kind → IntegralMixedVirtualContextScalarBits.Kind
  | .commonLeading => .commonLeading
  | .originalScale => .originalScale
noncomputable def physicalScalar (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (k : Kind) :=
  IntegralMixedPhysicalNativeScalarBits.machine P a (physicalFamily P D J) (physicalInput P a D J h) k
noncomputable def virtualScalar (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (k : Kind) :=
  IntegralMixedVirtualContextScalarBits.machine P a (virtualFamily P D J) (virtualInput P a D J h) (virtualKind k)
noncomputable def scalar (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (k : Kind) :=
  (physicalScalar P a D J h k).choose (virtualScalar P a D J h k)

noncomputable def oldHeight (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  (IntegralMixedFramedOldHeightBits.machine P a D J h.tables h.native h.represents).withGuard (selected P .clearedHeight) (selected_FP P a .clearedHeight)
noncomputable def height (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  IntegralMixedFramedNativeCurrentQHeightBits.machine P a D J (IntegralMixedFramedHeaderBits.routing P D)
    (routingAccess P a D J h) h.height
noncomputable def leading (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  IntegralMixedFramedScalarLeadingBits.machine P a D J h.leading

end LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits

namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem denominator_selected (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (q : List Bool) : (denominator P a D J h).selected q = true ↔ selected P .derivativeCoefficient q = true := by
  change (IntegralMixedPhysicalNativeDenominatorBits.selected P q || IntegralMixedVirtualContextDenominatorBits.selected P q) = true ↔ _
  rw [Bool.or_eq_true, IntegralMixedPhysicalNativeDenominatorBits.selected_iff,
    IntegralMixedVirtualContextDenominatorBits.selected_iff, selected_iff]
  unfold IntegralMixedVirtualContextBits.context
  constructor
  · rintro (⟨hv, hr, hp, hc⟩ | ⟨hv, hr, hp, hl, hu⟩)
    · exact ⟨hv, hr, hp, by omega, by omega⟩
    · exact ⟨hv, hr, hp, by omega, hu⟩
  · rintro ⟨hv, hr, hp, hl, hu⟩
    by_cases hc : get P .slot15 q = 1
    · exact Or.inl ⟨hv, hr, hp, hc⟩
    · exact Or.inr ⟨hv, hr, hp, by omega, hu⟩

theorem scalar_selected (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (k : Kind) (q : List Bool) : (scalar P a D J h k).selected q = true ↔
      selected P (IntegralMixedPhysicalNativeScalarBits.code k) q = true := by
  change (IntegralMixedPhysicalNativeScalarBits.selected P k q || IntegralMixedVirtualContextScalarBits.selected P (virtualKind k) q) = true ↔ _
  rw [Bool.or_eq_true, IntegralMixedPhysicalNativeScalarBits.selected_iff,
    IntegralMixedVirtualContextScalarBits.selected_iff, selected_iff]
  unfold IntegralMixedVirtualContextBits.context
  have HE : IntegralMixedVirtualContextScalarBits.code (virtualKind k) = IntegralMixedPhysicalNativeScalarBits.code k := by cases k <;> rfl
  rw [HE]
  constructor
  · rintro (⟨hv, hr, hp, hc⟩ | ⟨hv, hr, hp, hl, hu⟩)
    · exact ⟨hv, hr, hp, by omega, by omega⟩
    · exact ⟨hv, hr, hp, by omega, hu⟩
  · rintro ⟨hv, hr, hp, hl, hu⟩
    by_cases hc : get P .slot15 q = 1
    · exact Or.inl ⟨hv, hr, hp, hc⟩
    · exact Or.inr ⟨hv, hr, hp, by omega, hu⟩

theorem leading_selected (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (q : List Bool) : (leading P a D J h).selected q = selected P .originalCoefficient q := rfl

theorem height_selected (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (q : List Bool) : (height P a D J h).selected q = selected P .factorPower q := rfl

theorem oldHeight_selected (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (q : List Bool) : (oldHeight P a D J h).selected q = selected P .clearedHeight q := rfl

noncomputable def node0 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) : PhaseNode phase where
  machine := leading P a D J h
  code := 0
  selected_phase q hq := ((selected_iff P .originalCoefficient q).mp hq).2.2.1
noncomputable def node1 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) : PhaseNode phase where
  machine := denominator P a D J h
  code := 1
  selected_phase q hq := ((selected_iff P .derivativeCoefficient q).mp ((denominator_selected P a D J h q).mp hq)).2.2.1
noncomputable def node2 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) : PhaseNode phase where
  machine := oldHeight P a D J h
  code := 2
  selected_phase q hq := ((selected_iff P .clearedHeight q).mp hq).2.2.1
noncomputable def node3 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) : PhaseNode phase where
  machine := scalar P a D J h .commonLeading
  code := 3
  selected_phase q hq := ((selected_iff P .monomialFactor q).mp ((scalar_selected P a D J h .commonLeading q).mp hq)).2.2.1
noncomputable def node4 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) : PhaseNode phase where
  machine := height P a D J h
  code := 4
  selected_phase q hq := ((selected_iff P .factorPower q).mp hq).2.2.1
noncomputable def node5 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) : PhaseNode phase where
  machine := scalar P a D J h .originalScale
  code := 5
  selected_phase q hq := ((selected_iff P .productEntry q).mp ((scalar_selected P a D J h .originalScale q).mp hq)).2.2.1
end LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits

namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem physical_leading_replies (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (answer : List Bool → List Bool) (hp : IntegralMixedFramedProducerActualBits.Matches P D J answer)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    IntegralMixedPhysicalOldBankBits.RepliesAt P (physicalFamily P D J) (IntegralMixedFramedHeaderBits.routing P D) answer q := by
  exact IntegralMixedFramedHeightCurrentBits.leading_replies P D J answer hp q hv

theorem denominator_correct (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (answer : List Bool → List Bool) (hp : IntegralMixedFramedProducerActualBits.Matches P D J answer) :
    Correct (denominator P a D J h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · apply IntegralMixedPhysicalNativeDenominatorBits.correct P a (physicalFamily P D J) (physicalInput P a D J h)
      (IntegralMixedFramedPhysicalBits.geometry P D J)
      (IntegralMixedFramedHeaderBits.routing P D) (routingAccess P a D J h) h.physicalScales answer
    intro q hq
    exact physical_leading_replies P D J answer hp q ((IntegralMixedPhysicalNativeDenominatorBits.selected_iff P q).mp hq).1
  · apply IntegralMixedVirtualContextDenominatorBits.correct P a (virtualFamily P D J)
      (virtualInput P a D J h) (IntegralMixedFramedHistoryFamilyBits.geometry P D J)
      (IntegralMixedFramedHeaderBits.routing P D) (routingAccess P a D J h) h.virtualScales answer
    intro q hq
    exact IntegralMixedFramedHeightCurrentBits.leading_replies P D J answer hp q ((IntegralMixedVirtualContextDenominatorBits.selected_iff P q).mp hq).1

theorem oldHeight_correct (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (answer : List Bool → List Bool) (hp : IntegralMixedFramedProducerActualBits.Matches P D J answer) :
    Correct (oldHeight P a D J h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply withGuard_correct _ _ _ answer _ (IntegralMixedFramedOldHeightBits.correct_of_matches P a D J h.tables h.native h.represents answer hp)
  intro q hq
  have H := (selected_iff P .clearedHeight q).mp hq
  exact (IntegralMixedFramedNativeOldHeightBits.selected_iff P q).mpr ⟨H.1, H.2.1, H.2.2.1⟩

theorem leading_correct (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (answer : List Bool → List Bool) :
    Correct (leading P a D J h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedFramedScalarLeadingBits.correct P a D J h.leading answer
end LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits

namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def nodes (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  [node0 P a D J h, node1 P a D J h, node2 P a D J h, node3 P a D J h, node4 P a D J h, node5 P a D J h]
noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  phaseDispatch (nodes P a D J h) zero

attribute [local irreducible] denominator scalar IntegralMixedFramedScalarLeadingBits.value
  IntegralMixedFramedOldHeightBits.value IntegralMixedFramedNativeHeightBits.model

theorem nodes_distinct (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :
    ((nodes P a D J h).map PhaseNode.code).Nodup := by
  change ([0, 1, 2, 3, 4, 5] : List ℕ).Nodup
  decide

theorem machine_selected (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool) :
    (machine P a D J h).selected q = true := by
  change (_ || (_ || (_ || (_ || (_ || (_ || true)))))) = true
  simp only [Bool.or_true]

theorem model0 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool)
    (hq : selected P .originalCoefficient q = true) : (machine P a D J h).model q = IntegralMixedFramedScalarLeadingBits.value P D J q := by
  exact phaseDispatch_model_selected (nodes P a D J h) zero q (node0 P a D J h) (nodes_distinct P a D J h) (by exact List.mem_cons_self) hq

theorem model1 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool)
    (hq : selected P .derivativeCoefficient q = true) : (machine P a D J h).model q = (denominator P a D J h).model q := by
  exact phaseDispatch_model_selected (nodes P a D J h) zero q (node1 P a D J h) (nodes_distinct P a D J h) (by exact List.mem_cons_of_mem _ (List.mem_cons_self)) ((denominator_selected P a D J h q).mpr hq)

theorem model2 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool)
    (hq : selected P .clearedHeight q = true) : (machine P a D J h).model q = IntegralMixedFramedOldHeightBits.value P D J q := by
  exact phaseDispatch_model_selected (nodes P a D J h) zero q (node2 P a D J h) (nodes_distinct P a D J h) (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) hq

theorem model3 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool)
    (hq : selected P .monomialFactor q = true) : (machine P a D J h).model q = (scalar P a D J h .commonLeading).model q := by
  exact phaseDispatch_model_selected (nodes P a D J h) zero q (node3 P a D J h) (nodes_distinct P a D J h) (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))) ((scalar_selected P a D J h .commonLeading q).mpr hq)

theorem model4 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool)
    (hq : selected P .factorPower q = true) : (machine P a D J h).model q = IntegralMixedFramedNativeHeightBits.model P D J q := by
  exact phaseDispatch_model_selected (nodes P a D J h) zero q (node4 P a D J h) (nodes_distinct P a D J h) (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))) hq

theorem model5 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool)
    (hq : selected P .productEntry q = true) : (machine P a D J h).model q = (scalar P a D J h .originalScale).model q := by
  exact phaseDispatch_model_selected (nodes P a D J h) zero q (node5 P a D J h) (nodes_distinct P a D J h) (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))) ((scalar_selected P a D J h .originalScale q).mpr hq)

structure Replies (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (answer : List Bool → List Bool) : Prop where
  physical : IntegralMixedPhysicalScalarReplyBits.Matches P (physicalFamily P D J) answer
  virtual : IntegralMixedVirtualContextScalarReplyBits.Matches P (virtualFamily P D J) answer
  height : IntegralMixedFramedHeightCurrentBits.Matches P D J answer

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hp : IntegralMixedFramedProducerActualBits.Matches P D J answer) (he : Replies P D J answer) :
    Correct (machine P a D J h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply phaseDispatch_correct _ _ answer _ (zero_correct _ _)
  intro b hb
  simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact leading_correct P a D J h answer
  · exact denominator_correct P a D J h answer hp
  · exact oldHeight_correct P a D J h answer hp
  · simp only [node3]
    unfold scalar
    apply choose_correct
    · exact IntegralMixedPhysicalNativeScalarBits.correct_of_matches P a (physicalFamily P D J) (physicalInput P a D J h) .commonLeading answer he.physical
    · exact IntegralMixedVirtualContextScalarBits.correct_of_matches P a (virtualFamily P D J) (virtualInput P a D J h) .commonLeading answer he.virtual
  · exact IntegralMixedFramedNativeCurrentQHeightBits.correct_of_current P a D J h.tables h.native h.represents h.height answer hp he.height
  · simp only [node5]
    unfold scalar
    apply choose_correct
    · exact IntegralMixedPhysicalNativeScalarBits.correct_of_matches P a (physicalFamily P D J) (physicalInput P a D J h) .originalScale answer he.physical
    · exact IntegralMixedVirtualContextScalarBits.correct_of_matches P a (virtualFamily P D J) (virtualInput P a D J h) .originalScale answer he.virtual
end LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits
