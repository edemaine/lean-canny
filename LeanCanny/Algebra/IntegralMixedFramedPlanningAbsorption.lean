/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCutProbeTransport
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeSpace
/-! # Typed absorption of redundant resource planning

These identities concern the complete parameter, plan and fallback-data
packages. They do not identify query words under different task encodings.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPlanningAbsorption
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedNormalizationBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ)

theorem parameters (hh : IntegralMixedFramedRawHeight.rootCeiling P L F C=P.height)
    (hm : ∀root,requiredModulus P L F C root≤P.modulusBound root) : planned P L F C=P := by
  have HB : (fun root=>max (P.modulusBound root) (requiredModulus P L F C root))=P.modulusBound :=
    funext (fun root=>max_eq_left (hm root))
  unfold planned
  rw [hh,HB]

theorem plan_heq (hh : IntegralMixedFramedRawHeight.rootCeiling P L F C=P.height)
    (hm : ∀root,requiredModulus P L F C root≤P.modulusBound root) : HEq (plannedPlan P D L F C) D := by
  unfold plannedPlan planned
  have HB : (fun root=>max (P.modulusBound root) (requiredModulus P L F C root))=P.modulusBound :=
    funext (fun root=>max_eq_left (hm root))
  rw [hh,HB]

theorem data_heq (hh : IntegralMixedFramedRawHeight.rootCeiling P L F C=P.height)
    (hm : ∀root,requiredModulus P L F C root≤P.modulusBound root) : HEq (plannedData P D H L F C) H := by
  unfold plannedData plannedPlan planned
  have HB : (fun root=>max (P.modulusBound root) (requiredModulus P L F C root))=P.modulusBound :=
    funext (fun root=>max_eq_left (hm root))
  rw [hh,HB]

noncomputable def controlsTransport {P Q : Parameters} {D : Plan P} {E : Plan Q}
    {H : IntegralMixedFramedHistoryFamilyBits.Data P D} {J : IntegralMixedFramedHistoryFamilyBits.Data Q E}
    (hp : Q=P) (hd : HEq E D) (hh : HEq J H)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D H) :
    IntegralMixedFramedCurrentQNativeBits.Controls Q E J := by
  cases hp
  cases hd
  cases hh
  exact c

theorem boundsTransport {P Q : Parameters} {D : Plan P} {E : Plan Q}
    {H : IntegralMixedFramedHistoryFamilyBits.Data P D} {J : IntegralMixedFramedHistoryFamilyBits.Data Q E}
    (hp : Q=P) (hd : HEq E D) (hh : HEq J H)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D H)
    (b : IntegralMixedFramedCurrentQNativeBits.Bounds P D H c) :
    IntegralMixedFramedCurrentQNativeBits.Bounds Q E J (controlsTransport hp hd hh c) := by
  cases hp
  cases hd
  cases hh
  exact b

end LeanCanny.Algebra.IntegralMixedFramedPlanningAbsorption
