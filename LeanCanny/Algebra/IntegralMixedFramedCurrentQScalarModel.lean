/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarMachines
/-! # Current-Q scalar dispatch preserves actual models and closes current replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedPhysicalDenominatorBits.value IntegralMixedVirtualDenominatorBits.value

theorem denominator_physical (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (q : List Bool) (hq : selected P .derivativeCoefficient q = true) (hx : get P .slot15 q = 1) :
    (denominator P a D J h).model q = IntegralMixedPhysicalDenominatorBits.value P (physicalFamily P D J) q := by
  have H := (selected_iff P .derivativeCoefficient q).mp hq
  have HS := (IntegralMixedPhysicalNativeDenominatorBits.selected_iff P q).mpr ⟨H.1, H.2.1, H.2.2.1, hx⟩
  change (if IntegralMixedPhysicalNativeDenominatorBits.selected P q then _ else _) = _
  rw [HS]
  rfl

theorem denominator_virtual (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (q : List Bool) (hx : IntegralMixedVirtualContextBits.context P q) :
    (denominator P a D J h).model q = IntegralMixedVirtualDenominatorBits.value P (virtualFamily P D J) q := by
  have HN : IntegralMixedPhysicalNativeDenominatorBits.selected P q = false := by
    cases HH : IntegralMixedPhysicalNativeDenominatorBits.selected P q with
    | false => rfl
    | true => have H := ((IntegralMixedPhysicalNativeDenominatorBits.selected_iff P q).mp HH).2.2.2; unfold IntegralMixedVirtualContextBits.context at hx; omega
  change (if IntegralMixedPhysicalNativeDenominatorBits.selected P q then _ else _) = _
  rw [HN]
  rfl

theorem scalar_physical (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (k : Kind) (q : List Bool) (hq : selected P (IntegralMixedPhysicalNativeScalarBits.code k) q = true) (hx : get P .slot15 q = 1) :
    (scalar P a D J h k).model q = IntegralMixedPhysicalNativeScalarBits.value P (physicalFamily P D J) k q := by
  have H := (selected_iff P _ q).mp hq
  have HS := (IntegralMixedPhysicalNativeScalarBits.selected_iff P k q).mpr ⟨H.1, H.2.1, H.2.2.1, hx⟩
  change (if IntegralMixedPhysicalNativeScalarBits.selected P k q then _ else _) = _
  rw [HS]
  rfl

theorem scalar_virtual (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (k : Kind) (q : List Bool) (hx : IntegralMixedVirtualContextBits.context P q) :
    (scalar P a D J h k).model q = IntegralMixedVirtualContextScalarBits.value P (virtualFamily P D J) (virtualKind k) q := by
  have HN : IntegralMixedPhysicalNativeScalarBits.selected P k q = false := by
    cases HH : IntegralMixedPhysicalNativeScalarBits.selected P k q with
    | false => rfl
    | true => have H := ((IntegralMixedPhysicalNativeScalarBits.selected_iff P k q).mp HH).2.2.2; unfold IntegralMixedVirtualContextBits.context at hx; omega
  change (if IntegralMixedPhysicalNativeScalarBits.selected P k q then _ else _) = _
  rw [HN]
  rfl
end LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits

namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 0 →
    (1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) → phase q ≤ 5 → answer q = (machine P a D J h).model q

theorem physical_matches (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hm : Matches P a D J h answer) :
    IntegralMixedPhysicalScalarReplyBits.Matches P (physicalFamily P D J) answer := by
  intro p q hp hv hr hx hphase
  have HX : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := by omega
  have HS := (selected_iff P p q).mpr ⟨hv, hr, hphase, HX⟩
  rcases hp with rfl | rfl | rfl | rfl
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model0 P a D J h q HS).trans (IntegralMixedFramedScalarLeadingBits.physical_value P D J q))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model1 P a D J h q HS).trans (denominator_physical P a D J h q HS hx))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model3 P a D J h q HS).trans (scalar_physical P a D J h .commonLeading q HS hx))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model4 P a D J h q HS).trans (IntegralMixedFramedNativeHeightActualBits.physical_model P D J q hx))

theorem virtual_matches (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hm : Matches P a D J h answer) :
    IntegralMixedVirtualContextScalarReplyBits.Matches P (virtualFamily P D J) answer := by
  intro p q hp hv hr hx hphase
  have HX : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := ⟨by have := hx.1; omega, hx.2⟩
  have HS := (selected_iff P p q).mpr ⟨hv, hr, hphase, HX⟩
  rcases hp with rfl | rfl | rfl | rfl
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model0 P a D J h q HS).trans (IntegralMixedFramedScalarLeadingBits.virtual_value P D J q))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model1 P a D J h q HS).trans (denominator_virtual P a D J h q hx))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model3 P a D J h q HS).trans (scalar_virtual P a D J h .commonLeading q hx))
  · have HE := hm q hv hr HX (by rw [hphase]; decide)
    exact HE.trans ((model4 P a D J h q HS).trans (IntegralMixedFramedNativeHeightActualBits.virtual_model P D J q hx))

theorem height_matches (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hm : Matches P a D J h answer) : IntegralMixedFramedHeightCurrentBits.Matches P D J answer := by
  constructor
  intro q hs hx
  have H := (IntegralMixedFramedNativeOldHeightBits.selected_iff P q).mp hs
  have HS := (selected_iff P .clearedHeight q).mpr ⟨H.1, H.2.1, H.2.2, hx⟩
  exact (hm q H.1 H.2.1 hx (by rw [H.2.2]; decide)).trans (model2 P a D J h q HS)

theorem replies_of_matches (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hm : Matches P a D J h answer) : Replies P D J answer :=
  ⟨physical_matches P a D J h answer hm, virtual_matches P a D J h answer hm, height_matches P a D J h answer hm⟩

theorem correct_of_matches (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hp : IntegralMixedFramedProducerActualBits.Matches P D J answer) (hm : Matches P a D J h answer) :
    Correct (machine P a D J h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a D J h answer hp (replies_of_matches P a D J h answer hm)
end LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits

namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

private theorem choose_canonical (M N : Machine) (m : ℕ) (q : List Bool)
    (hm : ∃ z : ZMod m, residueBits z = M.model q) (hn : ∃ z : ZMod m, residueBits z = N.model q) :
    ∃ z : ZMod m, residueBits z = (M.choose N).model q := by
  change ∃ z : ZMod m, residueBits z = if M.selected q then M.model q else N.model q
  split_ifs <;> assumption

theorem denominator_canonical (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = (denominator P a D J h).model q :=
  choose_canonical _ _ _ q
    (IntegralMixedDenominatorCanonicalBits.physical P a (physicalFamily P D J) (physicalInput P a D J h)
      (IntegralMixedFramedPhysicalBits.geometry P D J) (IntegralMixedFramedHeaderBits.routing P D)
      (routingAccess P a D J h) h.physicalScales q)
    (IntegralMixedDenominatorCanonicalBits.virtual P a (virtualFamily P D J) (virtualInput P a D J h)
      (IntegralMixedFramedHistoryFamilyBits.geometry P D J) (IntegralMixedFramedHeaderBits.routing P D)
      (routingAccess P a D J h) h.virtualScales q)

theorem scalar_canonical (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (k : Kind) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = (scalar P a D J h k).model q :=
  choose_canonical _ _ _ q (IntegralMixedPhysicalNativeScalarBits.value_canonical P (physicalFamily P D J) k q)
    (IntegralMixedVirtualContextScalarBits.value_canonical P (virtualFamily P D J) (virtualKind k) q)

attribute [local irreducible] IntegralMixedFramedScalarLeadingBits.value
  IntegralMixedFramedOldHeightBits.value IntegralMixedFramedNativeHeightBits.model

theorem canonical (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = (machine P a D J h).model q := by
  change ∃ z : ZMod (modulus P q), residueBits z =
    ((leading P a D J h).choose ((denominator P a D J h).choose ((oldHeight P a D J h).choose
      ((scalar P a D J h .commonLeading).choose ((height P a D J h).choose ((scalar P a D J h .originalScale).choose zero)))))).model q
  exact choose_canonical (leading P a D J h)
    ((denominator P a D J h).choose ((oldHeight P a D J h).choose
      ((scalar P a D J h .commonLeading).choose ((height P a D J h).choose ((scalar P a D J h .originalScale).choose zero)))))
    (modulus P q) q (IntegralMixedFramedScalarLeadingBits.canonical P D J q)
    (choose_canonical (denominator P a D J h)
      ((oldHeight P a D J h).choose ((scalar P a D J h .commonLeading).choose
        ((height P a D J h).choose ((scalar P a D J h .originalScale).choose zero))))
      (modulus P q) q (denominator_canonical P a D J h q)
      (choose_canonical (oldHeight P a D J h)
        ((scalar P a D J h .commonLeading).choose ((height P a D J h).choose ((scalar P a D J h .originalScale).choose zero)))
        (modulus P q) q (IntegralMixedFramedOldHeightBits.value_canonical P D J q)
        (choose_canonical (scalar P a D J h .commonLeading)
          ((height P a D J h).choose ((scalar P a D J h .originalScale).choose zero))
          (modulus P q) q (scalar_canonical P a D J h .commonLeading q)
          (choose_canonical (height P a D J h) ((scalar P a D J h .originalScale).choose zero)
            (modulus P q) q (IntegralMixedFramedNativeHeightBits.model_canonical P D J q)
            (choose_canonical (scalar P a D J h .originalScale) zero (modulus P q) q
              (scalar_canonical P a D J h .originalScale q) ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩)))))
end LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits

namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def component (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) : Phase → List Bool → List Bool
  | .originalCoefficient => IntegralMixedFramedScalarLeadingBits.value P D J
  | .derivativeCoefficient => fun q => if get P .slot15 q = 1 then IntegralMixedPhysicalDenominatorBits.value P (physicalFamily P D J) q else IntegralMixedVirtualDenominatorBits.value P (virtualFamily P D J) q
  | .clearedHeight => IntegralMixedFramedOldHeightBits.value P D J
  | .monomialFactor => fun q => if get P .slot15 q = 1 then IntegralMixedPhysicalNativeScalarBits.value P (physicalFamily P D J) .commonLeading q else IntegralMixedVirtualContextScalarBits.value P (virtualFamily P D J) .commonLeading q
  | .factorPower => IntegralMixedFramedNativeHeightBits.model P D J
  | .productEntry => fun q => if get P .slot15 q = 1 then IntegralMixedPhysicalNativeScalarBits.value P (physicalFamily P D J) .originalScale q else IntegralMixedVirtualContextScalarBits.value P (virtualFamily P D J) .originalScale q
  | _ => fun _ => []

theorem model_phase (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (p : Phase) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 0)
    (hx : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) (hp : p.code ≤ 5) (hq : isPhase p q) :
    (machine P a D J h).model q = component P D J p q := by
  have HS := (selected_iff P p q).mpr ⟨hv, hr, hq, hx⟩
  have HT (hn : get P .slot15 q ≠ 1) : IntegralMixedVirtualContextBits.context P q := ⟨by omega, hx.2⟩
  cases p <;> norm_num [Phase.code] at hp
  case originalCoefficient => exact model0 P a D J h q HS
  case derivativeCoefficient =>
    rw [model1 P a D J h q HS]
    by_cases hc : get P .slot15 q = 1
    · exact (denominator_physical P a D J h q HS hc).trans (ite_eq_left hc).symm
    · exact (denominator_virtual P a D J h q (HT hc)).trans (ite_eq_right hc).symm
  case clearedHeight => exact model2 P a D J h q HS
  case monomialFactor =>
    rw [model3 P a D J h q HS]
    by_cases hc : get P .slot15 q = 1
    · exact (scalar_physical P a D J h .commonLeading q HS hc).trans (ite_eq_left hc).symm
    · exact (scalar_virtual P a D J h .commonLeading q (HT hc)).trans (ite_eq_right hc).symm
  case factorPower => exact model4 P a D J h q HS
  case productEntry =>
    rw [model5 P a D J h q HS]
    by_cases hc : get P .slot15 q = 1
    · exact (scalar_physical P a D J h .originalScale q HS hc).trans (ite_eq_left hc).symm
    · exact (scalar_virtual P a D J h .originalScale q (HT hc)).trans (ite_eq_right hc).symm

def InScope (P : Parameters) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧ 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4

theorem nodes_scope (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (b : PhaseNode phase) (hb : b ∈ nodes P a D J h) (q : List Bool) (hs : b.machine.selected q = true) : InScope P q := by
  simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · have H := (selected_iff P .originalCoefficient q).mp hs
    exact ⟨H.1, H.2.1, H.2.2.2⟩
  · have H := (selected_iff P .derivativeCoefficient q).mp ((denominator_selected P a D J h q).mp hs)
    exact ⟨H.1, H.2.1, H.2.2.2⟩
  · have H := (selected_iff P .clearedHeight q).mp hs
    exact ⟨H.1, H.2.1, H.2.2.2⟩
  · have H := (selected_iff P .monomialFactor q).mp ((scalar_selected P a D J h .commonLeading q).mp hs)
    exact ⟨H.1, H.2.1, H.2.2.2⟩
  · have H := (selected_iff P .factorPower q).mp hs
    exact ⟨H.1, H.2.1, H.2.2.2⟩
  · have H := (selected_iff P .productEntry q).mp ((scalar_selected P a D J h .originalScale q).mp hs)
    exact ⟨H.1, H.2.1, H.2.2.2⟩

theorem model_none (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (q : List Bool) (hn : ¬InScope P q) : (machine P a D J h).model q = [] := by
  apply phaseDispatch_model_none
  intro b hb
  cases hs : b.machine.selected q with
  | false => rfl
  | true => exact False.elim (hn (nodes_scope P a D J h b hb q hs))

theorem model_invalid (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (q : List Bool) (hv : ¬IntegralMixedVirtualCaps.valid P q) : (machine P a D J h).model q = [] :=
  model_none P a D J h q (fun H => hv H.1)

theorem model_other_routine (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q ≠ 0) : (machine P a D J h).model q = [] :=
  model_none P a D J h q (fun H => hr H.2.1)

theorem model_other_context (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (q : List Bool) (hx : ¬(1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4)) : (machine P a D J h).model q = [] :=
  model_none P a D J h q (fun H => hx H.2.2)

theorem model_other_phase (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (q : List Bool) (hp : 5 < phase q) : (machine P a D J h).model q = [] := by
  apply phaseDispatch_model_off
  change phase q ∉ ([0,1,2,3,4,5] : List ℕ)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega
end LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits

namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev ComponentMatches (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (answer : List Bool → List Bool) : Prop :=
  ∀ (p : Phase) (q : List Bool), p.code ≤ 5 → IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 0 →
    (1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) → isPhase p q → answer q = component P D J p q

theorem matches_of_components (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hm : ComponentMatches P D J answer) : Matches P a D J h answer := by
  intro q hv hr hx hp
  let p := IntegralMixedPhaseDecode.decode (phase q)
  have HC : p.code = phase q := IntegralMixedPhaseDecode.code _ (IntegralMixedRoutineTaskBits.phase_lt q)
  have HQ : isPhase p q := IntegralMixedPhaseDecode.task q
  have HP : p.code ≤ 5 := HC.trans_le hp
  exact (hm p q HP hv hr hx HQ).trans (model_phase P a D J h p q hv hr hx HP HQ).symm

theorem components_of_matches (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hm : Matches P a D J h answer) : ComponentMatches P D J answer := by
  intro p q hp hv hr hx hq
  have HP : phase q ≤ 5 := hq.trans_le hp
  exact (hm q hv hr hx HP).trans (model_phase P a D J h p q hv hr hx hp hq)

theorem correct_of_components (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hp : IntegralMixedFramedProducerActualBits.Matches P D J answer) (hm : ComponentMatches P D J answer) :
    Correct (machine P a D J h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct_of_matches P a D J h answer hp (matches_of_components P a D J h answer hm)

noncomputable def residue (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (q : List Bool) : ZMod (modulus P q) := Classical.choose (canonical P a D J h q)

theorem residue_value (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (q : List Bool) : residueBits (residue P a D J h q) = (machine P a D J h).model q := Classical.choose_spec (canonical P a D J h q)
end LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits

namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
theorem semantic_matches (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (answer : List Bool → List Bool) (own : Matches P a D J h answer) :
    IntegralMixedFramedScalarModelBits.Matches P D J answer := by
  intro p q hp hv hr hx hq
  rcases hp with hp | rfl
  · by_cases h1 : get P .slot15 q = 1
    · exact (physical_matches P a D J h answer own p q hp hv hr h1 hq).trans
        (IntegralMixedFramedScalarModelBits.component_physical P D J p q hp h1).symm
    · have h2 : IntegralMixedVirtualContextBits.context P q := ⟨by omega, hx.2⟩
      have hpv : IntegralMixedVirtualContextScalarReplyBits.allowed p := hp
      exact (virtual_matches P a D J h answer own p q hpv hv hr h2 hq).trans
        (IntegralMixedFramedScalarModelBits.component_virtual P D J p q hpv h2).symm
  · have hs := (selected_iff P .productEntry q).mpr ⟨hv, hr, hq, hx⟩
    have HE := (own q hv hr hx (by rw [hq]; decide)).trans (model5 P a D J h q hs)
    by_cases h1 : get P .slot15 q = 1
    · rw [IntegralMixedFramedScalarModelBits.component, ite_eq_left rfl, ite_eq_left h1]
      exact HE.trans (scalar_physical P a D J h .originalScale q hs h1)
    · have h2 : IntegralMixedVirtualContextBits.context P q := ⟨by omega, hx.2⟩
      rw [IntegralMixedFramedScalarModelBits.component, ite_eq_left rfl, ite_eq_right h1]
      exact HE.trans (scalar_virtual P a D J h .originalScale q h2)

-- Only the implementation of the slope leaf changes; actual component
-- meanings are the original six scalar values, including malformed words.
theorem component_eq_legacy (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (p : Phase) (q : List Bool) : component P D J p q=IntegralMixedFramedFullScalarBits.component P D J p q := by
  cases p <;> rfl
end LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarBits
