/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullScalarDispatcher
/-! # Context-specific actual models in the native full scalar dispatcher -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem denominator_physical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hq : selected P .derivativeCoefficient q = true) (hx : get P .slot15 q = 1) :
    (denominator P a D h).model q = IntegralMixedPhysicalDenominatorBits.value P (physicalFamily P D) q := by
  have H := (selected_iff P .derivativeCoefficient q).mp hq
  have HS := (IntegralMixedPhysicalNativeDenominatorBits.selected_iff P q).mpr ⟨H.1, H.2.1, H.2.2.1, hx⟩
  change (if IntegralMixedPhysicalNativeDenominatorBits.selected P q then _ else _) = _
  rw [HS]
  rfl

theorem denominator_virtual (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hx : IntegralMixedVirtualContextBits.context P q) :
    (denominator P a D h).model q = IntegralMixedVirtualDenominatorBits.value P (virtualFamily P D) q := by
  have HN : IntegralMixedPhysicalNativeDenominatorBits.selected P q = false := by
    cases HH : IntegralMixedPhysicalNativeDenominatorBits.selected P q with
    | false => rfl
    | true => have H := ((IntegralMixedPhysicalNativeDenominatorBits.selected_iff P q).mp HH).2.2.2; unfold IntegralMixedVirtualContextBits.context at hx; omega
  change (if IntegralMixedPhysicalNativeDenominatorBits.selected P q then _ else _) = _
  rw [HN]
  rfl

theorem scalar_physical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (k : Kind) (q : List Bool) (hq : selected P (IntegralMixedPhysicalNativeScalarBits.code k) q = true) (hx : get P .slot15 q = 1) :
    (scalar P a D h k).model q = IntegralMixedPhysicalNativeScalarBits.value P (physicalFamily P D) k q := by
  have H := (selected_iff P _ q).mp hq
  have HS := (IntegralMixedPhysicalNativeScalarBits.selected_iff P k q).mpr ⟨H.1, H.2.1, H.2.2.1, hx⟩
  change (if IntegralMixedPhysicalNativeScalarBits.selected P k q then _ else _) = _
  rw [HS]
  rfl

theorem scalar_virtual (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (k : Kind) (q : List Bool) (hx : IntegralMixedVirtualContextBits.context P q) :
    (scalar P a D h k).model q = IntegralMixedVirtualContextScalarBits.value P (virtualFamily P D) (virtualKind k) q := by
  have HN : IntegralMixedPhysicalNativeScalarBits.selected P k q = false := by
    cases HH : IntegralMixedPhysicalNativeScalarBits.selected P k q with
    | false => rfl
    | true => have H := ((IntegralMixedPhysicalNativeScalarBits.selected_iff P k q).mp HH).2.2.2; unfold IntegralMixedVirtualContextBits.context at hx; omega
  change (if IntegralMixedPhysicalNativeScalarBits.selected P k q then _ else _) = _
  rw [HN]
  rfl
end LeanCanny.Algebra.IntegralMixedFullScalarBits
