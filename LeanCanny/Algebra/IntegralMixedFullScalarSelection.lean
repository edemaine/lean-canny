/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullScalarMachines
/-! # Disjoint context and phase selection for the full scalar routine -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem denominator_selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (q : List Bool) : (denominator P a D h).selected q = true ↔ selected P .derivativeCoefficient q = true := by
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

theorem scalar_selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (k : Kind) (q : List Bool) : (scalar P a D h k).selected q = true ↔
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

theorem leading_selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (q : List Bool) : (leading P a D h).selected q = selected P .originalCoefficient q := rfl

theorem height_selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (q : List Bool) : (height P a D h).selected q = selected P .factorPower q := rfl

theorem oldHeight_selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (q : List Bool) : (oldHeight P a D h).selected q = selected P .clearedHeight q := rfl

noncomputable def node0 (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) : PhaseNode phase where
  machine := leading P a D h
  code := 0
  selected_phase q hq := ((selected_iff P .originalCoefficient q).mp hq).2.2.1
noncomputable def node1 (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) : PhaseNode phase where
  machine := denominator P a D h
  code := 1
  selected_phase q hq := ((selected_iff P .derivativeCoefficient q).mp ((denominator_selected P a D h q).mp hq)).2.2.1
noncomputable def node2 (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) : PhaseNode phase where
  machine := oldHeight P a D h
  code := 2
  selected_phase q hq := ((selected_iff P .clearedHeight q).mp hq).2.2.1
noncomputable def node3 (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) : PhaseNode phase where
  machine := scalar P a D h .commonLeading
  code := 3
  selected_phase q hq := ((selected_iff P .monomialFactor q).mp ((scalar_selected P a D h .commonLeading q).mp hq)).2.2.1
noncomputable def node4 (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) : PhaseNode phase where
  machine := height P a D h
  code := 4
  selected_phase q hq := ((selected_iff P .factorPower q).mp hq).2.2.1
noncomputable def node5 (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) : PhaseNode phase where
  machine := scalar P a D h .originalScale
  code := 5
  selected_phase q hq := ((selected_iff P .productEntry q).mp ((scalar_selected P a D h .originalScale q).mp hq)).2.2.1
end LeanCanny.Algebra.IntegralMixedFullScalarBits
