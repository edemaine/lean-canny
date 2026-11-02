/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedProducerCurrent
public import LeanCanny.Algebra.IntegralMixedFramedCompanionSource
public import LeanCanny.Algebra.IntegralMixedPhysicalProducerActual
/-! # Actual source-framed producer models and literal creating leading values -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedProducerActualBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (Plan instruction)
open IntegralMixedFramedProducerBits (physicalFamily virtualFamily)
open scoped Classical

noncomputable def leading (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : List Bool :=
  if get P .slot15 q=0 then IntegralMixedIntegerFamilyBits.leadingValue P (IntegralMixedFramedIntegerBits.polynomial P D) q
  else if get P .slot15 q=1 then IntegralMixedPhysicalProducerLeadingBits.value P (physicalFamily P D H) q
  else IntegralMixedNormalizationTopBits.leadingValue P (virtualFamily P D H) q

noncomputable def companion (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : List Bool :=
  if get P .slot15 q=0 then IntegralMixedIntegerFamilyBits.companionValue P (virtualFamily P D H) (IntegralMixedFramedIntegerBits.polynomial P D) q
  else if get P .slot15 q=1 then IntegralMixedPhysicalCompanionBits.companionValue P (physicalFamily P D H) q
  else IntegralMixedNormalizedCompanionBits.companionValue P (virtualFamily P D H) q

structure Matches (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (answer : List Bool → List Bool) : Prop where
  leading : ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q=6 →
    get P .slot15 q≤4 → phase q=0 → answer q=leading P D H q
  companion : ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q=6 →
    get P .slot15 q≤4 → phase q=26 → answer q=companion P D H q

theorem leading_actual (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (hx : get P .slot15 q=(instruction P D (IntegralMixedVirtualTaskBits.saved P q)).command.context) :
    leading P D H q=residueBits (IntegralMixedFramedCompanionBits.leading P D H (IntegralMixedVirtualTaskBits.saved P q) : ZMod (modulus P q)) := by
  cases hc : (instruction P D (IntegralMixedVirtualTaskBits.saved P q)).command with
  | integer p hp hd =>
    have HX : get P .slot15 q=0 := by simpa only [hc,IntegralMixedFullHistoryScript.Command.context] using hx
    rw [leading,ite_eq_left HX]
    unfold IntegralMixedIntegerFamilyBits.leadingValue IntegralMixedIntegerFamilyBits.taskPolynomial
    rw [IntegralMixedFramedIntegerBits.polynomial_actual P D _ p hp hd hc]
    unfold IntegralMixedFramedCompanionBits.leading
    rw [hc]
    rfl
  | critical r =>
    have HX : get P .slot15 q=1 := by simpa only [hc,IntegralMixedFullHistoryScript.Command.context] using hx
    rw [leading,ite_eq_right (by omega : ¬get P .slot15 q=0),ite_eq_left HX,
      IntegralMixedPhysicalProducerLeadingBits.value_actual]
    change residueBits (criticalLeading ((virtualFamily P D H).state (IntegralMixedVirtualTaskBits.saved P q))
      ((virtualFamily P D H).birth_bound _) (IntegralMixedFramedPhysicalBits.rule P D (IntegralMixedVirtualTaskBits.saved P q)) : ZMod (modulus P q))=_
    rw [IntegralMixedFramedPhysicalBits.rule_critical P D _ r hc]
    unfold IntegralMixedFramedCompanionBits.leading
    rw [hc]
    rfl
  | cut r k d ha hd =>
    have HX : 2≤get P .slot15 q := by
      rw [hx,hc]
      cases k <;> norm_num [IntegralMixedFullHistoryScript.Command.context]
    rw [leading,ite_eq_right (by omega : ¬get P .slot15 q=0),ite_eq_right (by omega : ¬get P .slot15 q=1)]
    unfold IntegralMixedNormalizationTopBits.leadingValue
    rw [← IntegralMixedNormalizationTopBits.top_normalized_leading]
    have HS : IntegralMixedFramedHistoryFamilyBits.selection P D H (IntegralMixedVirtualTaskBits.saved P q)=⟨r,k,d,ha⟩ := by
      unfold IntegralMixedFramedHistoryFamilyBits.selection
      rw [hc]
    change residueBits (normalizedScalarLeading ((virtualFamily P D H).state (IntegralMixedVirtualTaskBits.saved P q))
      (IntegralMixedCutMatrix.raw ((virtualFamily P D H).state (IntegralMixedVirtualTaskBits.saved P q)) ((virtualFamily P D H).birth_bound _)
        (IntegralMixedFramedHistoryFamilyBits.selection P D H _).rule (IntegralMixedFramedHistoryFamilyBits.selection P D H _).kind
        (IntegralMixedFramedHistoryFamilyBits.selection P D H _).degree) (IntegralMixedFramedHistoryFamilyBits.selection P D H _).degree : ZMod (modulus P q))=_
    rw [HS]
    unfold IntegralMixedFramedCompanionBits.leading
    rw [hc]
    rfl

end LeanCanny.Algebra.IntegralMixedFramedProducerActualBits
