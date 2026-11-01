/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullScalarCanonical
/-! # Actual scalar phase models and zero extension -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def component (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) : Phase → List Bool → List Bool
  | .originalCoefficient => IntegralMixedFullScalarLeadingBits.value P D
  | .derivativeCoefficient => fun q => if get P .slot15 q = 1 then IntegralMixedPhysicalDenominatorBits.value P (physicalFamily P D) q else IntegralMixedVirtualDenominatorBits.value P (virtualFamily P D) q
  | .clearedHeight => IntegralMixedOldHeightBits.value P D
  | .monomialFactor => fun q => if get P .slot15 q = 1 then IntegralMixedPhysicalNativeScalarBits.value P (physicalFamily P D) .commonLeading q else IntegralMixedVirtualContextScalarBits.value P (virtualFamily P D) .commonLeading q
  | .factorPower => IntegralMixedNativeHeightBits.model P D
  | .productEntry => fun q => if get P .slot15 q = 1 then IntegralMixedPhysicalNativeScalarBits.value P (physicalFamily P D) .originalScale q else IntegralMixedVirtualContextScalarBits.value P (virtualFamily P D) .originalScale q
  | _ => fun _ => []

theorem model_phase (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (p : Phase) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 0)
    (hx : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) (hp : p.code ≤ 5) (hq : isPhase p q) :
    (machine P a D h).model q = component P D p q := by
  have HS := (selected_iff P p q).mpr ⟨hv, hr, hq, hx⟩
  have HT (hn : get P .slot15 q ≠ 1) : IntegralMixedVirtualContextBits.context P q := ⟨by omega, hx.2⟩
  cases p <;> norm_num [Phase.code] at hp
  case originalCoefficient => exact model0 P a D h q HS
  case derivativeCoefficient =>
    rw [model1 P a D h q HS]
    by_cases hc : get P .slot15 q = 1
    · exact (denominator_physical P a D h q HS hc).trans (ite_eq_left hc).symm
    · exact (denominator_virtual P a D h q (HT hc)).trans (ite_eq_right hc).symm
  case clearedHeight => exact model2 P a D h q HS
  case monomialFactor =>
    rw [model3 P a D h q HS]
    by_cases hc : get P .slot15 q = 1
    · exact (scalar_physical P a D h .commonLeading q HS hc).trans (ite_eq_left hc).symm
    · exact (scalar_virtual P a D h .commonLeading q (HT hc)).trans (ite_eq_right hc).symm
  case factorPower => exact model4 P a D h q HS
  case productEntry =>
    rw [model5 P a D h q HS]
    by_cases hc : get P .slot15 q = 1
    · exact (scalar_physical P a D h .originalScale q HS hc).trans (ite_eq_left hc).symm
    · exact (scalar_virtual P a D h .originalScale q (HT hc)).trans (ite_eq_right hc).symm

def InScope (P : Parameters) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧ 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4

theorem nodes_scope (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (b : PhaseNode phase) (hb : b ∈ nodes P a D h) (q : List Bool) (hs : b.machine.selected q = true) : InScope P q := by
  simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · have H := (selected_iff P .originalCoefficient q).mp hs
    exact ⟨H.1, H.2.1, H.2.2.2⟩
  · have H := (selected_iff P .derivativeCoefficient q).mp ((denominator_selected P a D h q).mp hs)
    exact ⟨H.1, H.2.1, H.2.2.2⟩
  · have H := (selected_iff P .clearedHeight q).mp hs
    exact ⟨H.1, H.2.1, H.2.2.2⟩
  · have H := (selected_iff P .monomialFactor q).mp ((scalar_selected P a D h .commonLeading q).mp hs)
    exact ⟨H.1, H.2.1, H.2.2.2⟩
  · have H := (selected_iff P .factorPower q).mp hs
    exact ⟨H.1, H.2.1, H.2.2.2⟩
  · have H := (selected_iff P .productEntry q).mp ((scalar_selected P a D h .originalScale q).mp hs)
    exact ⟨H.1, H.2.1, H.2.2.2⟩

theorem model_none (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hn : ¬InScope P q) : (machine P a D h).model q = [] := by
  apply phaseDispatch_model_none
  intro b hb
  cases hs : b.machine.selected q with
  | false => rfl
  | true => exact False.elim (hn (nodes_scope P a D h b hb q hs))

theorem model_invalid (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hv : ¬IntegralMixedVirtualCaps.valid P q) : (machine P a D h).model q = [] :=
  model_none P a D h q (fun H => hv H.1)

theorem model_other_routine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q ≠ 0) : (machine P a D h).model q = [] :=
  model_none P a D h q (fun H => hr H.2.1)

theorem model_other_context (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hx : ¬(1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4)) : (machine P a D h).model q = [] :=
  model_none P a D h q (fun H => hx H.2.2)

theorem model_other_phase (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hp : 5 < phase q) : (machine P a D h).model q = [] := by
  apply phaseDispatch_model_off
  change phase q ∉ ([0,1,2,3,4,5] : List ℕ)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega
end LeanCanny.Algebra.IntegralMixedFullScalarBits
