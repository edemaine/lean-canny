/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalCompanionCurrent
public import LeanCanny.Algebra.IntegralMixedFullHistoryCompanionMatrix
/-! # Actual physical native companions use the full history's creating polynomial -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev fullFamily (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) :=
  IntegralMixedFullPhysicalBits.family P (IntegralMixedFullHistoryFamilyBits.physicalData P D)

theorem rule_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (r : CriticalRule (P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q))))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedPhysicalTaskBits.saved P q) = some (.critical r)) :
    (fullFamily P D).rule (IntegralMixedPhysicalTaskBits.saved P q) = r :=
  IntegralMixedFullPhysicalBits.rule_critical P (IntegralMixedFullHistoryFamilyBits.physicalData P D) _ r
    ((IntegralMixedFullHistoryFamilyBits.physical_creating P D _).trans hc)

theorem polynomial_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (r : CriticalRule (P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q))))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedPhysicalTaskBits.saved P q) = some (.critical r))
    (hcoord : get P .slot13 q = r.coordinate % (P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q)) - r.offset.val + 1)) :
    letI := (family P (fullFamily P D)).ring q
    (family P (fullFamily P D)).polynomial q =
      (IntegralMixedFullHistoryCompanionBits.source P D).polynomial (IntegralMixedVirtualTaskBits.saved P q) := by
  let _ := (family P (fullFamily P D)).ring q
  have HR := rule_creating P D q r hc
  have HC : ((IntegralMixedPhysicalTaskBits.indices P (fullFamily P D)).coordinate q).val =
      ((fullFamily P D).rule (IntegralMixedPhysicalTaskBits.saved P q)).coordinate %
        ((fullFamily P D).ambient (IntegralMixedPhysicalTaskBits.saved P q) -
          ((fullFamily P D).rule (IntegralMixedPhysicalTaskBits.saved P q)).offset.val + 1) := by
    change get P .slot13 q % ((fullFamily P D).ambient (IntegralMixedPhysicalTaskBits.saved P q) -
      ((fullFamily P D).rule (IntegralMixedPhysicalTaskBits.saved P q)).offset.val + 1) = _
    rw [HR]
    rw [hcoord]
    exact Nat.mod_mod _ _
  have HP := actual_polynomial P (fullFamily P D) q HC
  rw [HR] at HP
  change (family P (fullFamily P D)).polynomial q =
    (IntegralMixedFullHistoryCompanionBits.source P D).polynomial (IntegralMixedPhysicalTaskBits.saved P q)
  rw [IntegralMixedFullHistoryCompanionBits.polynomial_creating P D _ (.critical r) hc]
  exact HP

theorem degree_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (r : CriticalRule (P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q))))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedPhysicalTaskBits.saved P q) = some (.critical r)) :
    (family P (fullFamily P D)).degree q =
      (IntegralMixedFullHistoryCompanionBits.source P D).degree (IntegralMixedVirtualTaskBits.saved P q) := by
  change (family P (fullFamily P D)).degree q =
    (IntegralMixedFullHistoryCompanionBits.source P D).degree (IntegralMixedPhysicalTaskBits.saved P q)
  rw [IntegralMixedFullHistoryCompanionBits.degree_creating P D _ (.critical r) hc]
  change PurePowerReductionBounds.dimension
      ((fullFamily P D).ambient (IntegralMixedPhysicalTaskBits.saved P q) -
        ((fullFamily P D).rule (IntegralMixedPhysicalTaskBits.saved P q)).offset.val + 1)
      ((fullFamily P D).spatial (IntegralMixedPhysicalTaskBits.saved P q)).degree =
    PurePowerReductionBounds.dimension (P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q)) - r.offset.val + 1)
      (D.spatial (pairFst (IntegralMixedPhysicalTaskBits.saved P q))).degree
  rw [rule_creating P D q r hc]
  rfl

theorem matrix_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (r : CriticalRule (P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q))))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedPhysicalTaskBits.saved P q) = some (.critical r))
    (hcoord : get P .slot13 q = r.coordinate % (P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q)) - r.offset.val + 1)) :
    (family P (fullFamily P D)).matrix q =
      (IntegralMixedFullHistoryCompanionBits.source P D).matrix (IntegralMixedVirtualTaskBits.saved P q) := by
  rw [IntegralMixedFullHistoryCompanionBits.source_matrix]
  change IntegralMixedFullHistoryCompanionBits.matrixAt P D (IntegralMixedVirtualTaskBits.saved P q)
      ((family P (fullFamily P D)).polynomial q) ((family P (fullFamily P D)).degree q) = _
  exact congrArg₂ (IntegralMixedFullHistoryCompanionBits.matrixAt P D (IntegralMixedVirtualTaskBits.saved P q))
    (polynomial_creating P D q r hc hcoord) (degree_creating P D q r hc)

theorem value_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (r : CriticalRule (P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q))))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedPhysicalTaskBits.saved P q) = some (.critical r))
    (hcoord : get P .slot13 q = r.coordinate % (P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q)) - r.offset.val + 1)) :
    companionValue P (fullFamily P D) q = IntegralMixedFullHistoryCompanionBits.value P D q := by
  unfold companionValue PaddedIntegralGeneratorFinBits.Family.value
  rw [matrix_creating P D q r hc hcoord]
  rfl

end LeanCanny.Algebra.IntegralMixedPhysicalCompanionBits
