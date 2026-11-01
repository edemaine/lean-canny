/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerProducerNative
public import LeanCanny.Algebra.IntegralMixedFullHistoryCompanionMatrix
/-! # Native integer companions equal the literal creating-command matrix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerProducerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
set_option backward.isDefEq.respectTransparency false

theorem polynomial_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (p : Polynomial ℤ) (hp : p ≠ 0) (hd : p.natDegree ≤ 2 ^ P.width (pairFst (IntegralMixedVirtualTaskBits.saved P q)))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) = some (.integer p hp hd)) :
    letI := (family P D).ring q
    (family P D).polynomial q = (IntegralMixedFullHistoryCompanionBits.source P D).polynomial (IntegralMixedVirtualTaskBits.saved P q) := by
  let _ := (family P D).ring q
  rw [IntegralMixedFullHistoryCompanionBits.polynomial_creating P D _ (.integer p hp hd) hc]
  change (polynomial P D (IntegralMixedVirtualTaskBits.saved P q)).map (Int.castRingHom ((family P D).carrier q)) =
    p.map (Int.castRingHom ((family P D).carrier q))
  rw [polynomial_actual P D _ p hp hd hc]

theorem degree_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (p : Polynomial ℤ) (hp : p ≠ 0) (hd : p.natDegree ≤ 2 ^ P.width (pairFst (IntegralMixedVirtualTaskBits.saved P q)))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) = some (.integer p hp hd)) :
    (family P D).degree q = (IntegralMixedFullHistoryCompanionBits.source P D).degree (IntegralMixedVirtualTaskBits.saved P q) := by
  rw [IntegralMixedFullHistoryCompanionBits.degree_creating P D _ (.integer p hp hd) hc]
  change (polynomial P D (IntegralMixedVirtualTaskBits.saved P q)).natDegree = p.natDegree
  rw [polynomial_actual P D _ p hp hd hc]

theorem matrix_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (p : Polynomial ℤ) (hp : p ≠ 0) (hd : p.natDegree ≤ 2 ^ P.width (pairFst (IntegralMixedVirtualTaskBits.saved P q)))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) = some (.integer p hp hd)) :
    (family P D).matrix q = (IntegralMixedFullHistoryCompanionBits.source P D).matrix (IntegralMixedVirtualTaskBits.saved P q) := by
  rw [IntegralMixedFullHistoryCompanionBits.source_matrix]
  change IntegralMixedFullHistoryCompanionBits.matrixAt P D (IntegralMixedVirtualTaskBits.saved P q)
      ((family P D).polynomial q) ((family P D).degree q) = _
  exact congrArg₂ (IntegralMixedFullHistoryCompanionBits.matrixAt P D (IntegralMixedVirtualTaskBits.saved P q))
    (polynomial_creating P D q p hp hd hc) (degree_creating P D q p hp hd hc)

theorem value_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (p : Polynomial ℤ) (hp : p ≠ 0) (hd : p.natDegree ≤ 2 ^ P.width (pairFst (IntegralMixedVirtualTaskBits.saved P q)))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) = some (.integer p hp hd)) :
    companionValue P D q = IntegralMixedFullHistoryCompanionBits.value P D q := by
  unfold companionValue PaddedIntegralGeneratorFinBits.Family.value
  rw [matrix_creating P D q p hp hd hc]
  rfl

end LeanCanny.Algebra.IntegralMixedIntegerProducerBits
