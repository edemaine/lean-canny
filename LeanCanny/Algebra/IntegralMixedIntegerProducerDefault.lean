/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedProducerLeadingActual
/-! # Missing chronological producers use the literal integer-X padding command -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerProducerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
set_option backward.isDefEq.respectTransparency false

theorem polynomial_none (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool)
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D key = none) : polynomial P D key = Polynomial.X := by
  unfold polynomial
  rw [hc]

theorem polynomial_default (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) = none) :
    letI := (family P D).ring q
    (family P D).polynomial q = (IntegralMixedFullHistoryCompanionBits.source P D).polynomial (IntegralMixedVirtualTaskBits.saved P q) := by
  let _ := (family P D).ring q
  have HG : (IntegralMixedFullHistoryCompanionBits.source P D).polynomial (IntegralMixedVirtualTaskBits.saved P q) =
      (Polynomial.X : Polynomial ((family P D).carrier q)) := by
    change IntegralMixedFullHistoryScript.polynomial ((bank P D).state (IntegralMixedVirtualTaskBits.saved P q))
      ((bank P D).birth_bound (IntegralMixedVirtualTaskBits.saved P q))
      ((IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q)).getD defaultCommand) = _
    rw [hc]
    simp only [Option.getD_none, defaultCommand, IntegralMixedFullHistoryScript.polynomial, Polynomial.map_X]
  rw [HG]
  change (polynomial P D (IntegralMixedVirtualTaskBits.saved P q)).map (Int.castRingHom ((family P D).carrier q)) = _
  rw [polynomial_none P D _ hc, Polynomial.map_X]

theorem degree_default (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) = none) :
    (family P D).degree q = (IntegralMixedFullHistoryCompanionBits.source P D).degree (IntegralMixedVirtualTaskBits.saved P q) := by
  have HG : (IntegralMixedFullHistoryCompanionBits.source P D).degree (IntegralMixedVirtualTaskBits.saved P q) = 1 := by
    change IntegralMixedFullHistoryScript.degree ((bank P D).state (IntegralMixedVirtualTaskBits.saved P q))
      ((bank P D).birth_bound (IntegralMixedVirtualTaskBits.saved P q))
      ((IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q)).getD defaultCommand) = _
    rw [hc]
    simp only [Option.getD_none, defaultCommand, IntegralMixedFullHistoryScript.degree, Polynomial.natDegree_X]
  rw [HG]
  change (polynomial P D (IntegralMixedVirtualTaskBits.saved P q)).natDegree = 1
  rw [polynomial_none P D _ hc, Polynomial.natDegree_X]

theorem matrix_default (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) = none) :
    (family P D).matrix q = (IntegralMixedFullHistoryCompanionBits.source P D).matrix (IntegralMixedVirtualTaskBits.saved P q) := by
  rw [IntegralMixedFullHistoryCompanionBits.source_matrix]
  change IntegralMixedFullHistoryCompanionBits.matrixAt P D (IntegralMixedVirtualTaskBits.saved P q)
      ((family P D).polynomial q) ((family P D).degree q) = _
  exact congrArg₂ (IntegralMixedFullHistoryCompanionBits.matrixAt P D (IntegralMixedVirtualTaskBits.saved P q))
    (polynomial_default P D q hc) (degree_default P D q hc)

theorem value_default (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) = none) :
    companionValue P D q = IntegralMixedFullHistoryCompanionBits.value P D q := by
  unfold companionValue PaddedIntegralGeneratorFinBits.Family.value
  rw [matrix_default P D q hc]
  rfl

theorem leading_default (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) = none) :
    leadingValue P D q = residueBits (IntegralMixedFullHistoryCompanionBits.leading P D (IntegralMixedVirtualTaskBits.saved P q) : ZMod (modulus P q)) := by
  unfold leadingValue leadingInteger IntegralMixedFullHistoryCompanionBits.leading IntegralMixedFullHistoryFamilyBits.creatingCommand
  rw [polynomial_none P D _ hc, hc]
  rfl

end LeanCanny.Algebra.IntegralMixedIntegerProducerBits
