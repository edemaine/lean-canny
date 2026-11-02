/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullScalarDispatcher
/-! # Context-specific actual models in the native full scalar dispatcher -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullScalarBits
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
end LeanCanny.Algebra.IntegralMixedFramedFullScalarBits
