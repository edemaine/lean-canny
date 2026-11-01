/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionCurrent
public import LeanCanny.Algebra.IntegralMixedFullHistoryCompanionMatrix
/-! # Normalized native companions equal literal creating cut commands -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizedCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev fullFamily (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) :=
  IntegralMixedFullHistoryFamilyBits.family P D

theorem polynomial_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (r : IntegralMixedCriticalSweep.Rule (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q))))
    (k : IntegralMixedRelativeCuts.Kind (D.spatial (pairFst (IntegralMixedVirtualTaskBits.saved P q))) r) (d : ℕ)
    (ha : d ≤ IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)
      (D.spatial (pairFst (IntegralMixedVirtualTaskBits.saved P q))).degree)
    (hd : d ≤ 2 ^ P.width (pairFst (IntegralMixedVirtualTaskBits.saved P q)))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) = some (.cut r k d ha hd)) :
    letI := (family P (fullFamily P D)).ring q
    (family P (fullFamily P D)).polynomial q =
      (IntegralMixedFullHistoryCompanionBits.source P D).polynomial (IntegralMixedVirtualTaskBits.saved P q) := by
  let _ := (family P (fullFamily P D)).ring q
  have HS := IntegralMixedFullHistoryFamilyBits.selection_cut P D (IntegralMixedVirtualTaskBits.saved P q) r k d ha hd hc
  rw [IntegralMixedFullHistoryCompanionBits.polynomial_creating P D _ (.cut r k d ha hd) hc]
  change normalizedScalarPolynomial ((fullFamily P D).state (IntegralMixedVirtualTaskBits.saved P q))
    (IntegralMixedCutMatrix.raw ((fullFamily P D).state (IntegralMixedVirtualTaskBits.saved P q))
      ((fullFamily P D).birth_bound (IntegralMixedVirtualTaskBits.saved P q))
      (IntegralMixedFullHistoryFamilyBits.selection P D (IntegralMixedVirtualTaskBits.saved P q)).rule
      (IntegralMixedFullHistoryFamilyBits.selection P D (IntegralMixedVirtualTaskBits.saved P q)).kind
      (IntegralMixedFullHistoryFamilyBits.selection P D (IntegralMixedVirtualTaskBits.saved P q)).degree)
    (IntegralMixedFullHistoryFamilyBits.selection P D (IntegralMixedVirtualTaskBits.saved P q)).degree = _
  rw [HS]
  rfl

theorem degree_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (r : IntegralMixedCriticalSweep.Rule (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q))))
    (k : IntegralMixedRelativeCuts.Kind (D.spatial (pairFst (IntegralMixedVirtualTaskBits.saved P q))) r) (d : ℕ)
    (ha : d ≤ IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)
      (D.spatial (pairFst (IntegralMixedVirtualTaskBits.saved P q))).degree)
    (hd : d ≤ 2 ^ P.width (pairFst (IntegralMixedVirtualTaskBits.saved P q)))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) = some (.cut r k d ha hd)) :
    (family P (fullFamily P D)).degree q =
      (IntegralMixedFullHistoryCompanionBits.source P D).degree (IntegralMixedVirtualTaskBits.saved P q) := by
  rw [IntegralMixedFullHistoryCompanionBits.degree_creating P D _ (.cut r k d ha hd) hc]
  change (IntegralMixedFullHistoryFamilyBits.selection P D (IntegralMixedVirtualTaskBits.saved P q)).degree = d
  rw [IntegralMixedFullHistoryFamilyBits.selection_cut P D _ r k d ha hd hc]

theorem matrix_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (r : IntegralMixedCriticalSweep.Rule (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q))))
    (k : IntegralMixedRelativeCuts.Kind (D.spatial (pairFst (IntegralMixedVirtualTaskBits.saved P q))) r) (d : ℕ)
    (ha : d ≤ IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)
      (D.spatial (pairFst (IntegralMixedVirtualTaskBits.saved P q))).degree)
    (hd : d ≤ 2 ^ P.width (pairFst (IntegralMixedVirtualTaskBits.saved P q)))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) = some (.cut r k d ha hd)) :
    (family P (fullFamily P D)).matrix q =
      (IntegralMixedFullHistoryCompanionBits.source P D).matrix (IntegralMixedVirtualTaskBits.saved P q) := by
  rw [IntegralMixedFullHistoryCompanionBits.source_matrix]
  change IntegralMixedFullHistoryCompanionBits.matrixAt P D (IntegralMixedVirtualTaskBits.saved P q)
      ((family P (fullFamily P D)).polynomial q) ((family P (fullFamily P D)).degree q) = _
  exact congrArg₂ (IntegralMixedFullHistoryCompanionBits.matrixAt P D (IntegralMixedVirtualTaskBits.saved P q))
    (polynomial_creating P D q r k d ha hd hc) (degree_creating P D q r k d ha hd hc)

theorem value_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (r : IntegralMixedCriticalSweep.Rule (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q))))
    (k : IntegralMixedRelativeCuts.Kind (D.spatial (pairFst (IntegralMixedVirtualTaskBits.saved P q))) r) (d : ℕ)
    (ha : d ≤ IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)
      (D.spatial (pairFst (IntegralMixedVirtualTaskBits.saved P q))).degree)
    (hd : d ≤ 2 ^ P.width (pairFst (IntegralMixedVirtualTaskBits.saved P q)))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) = some (.cut r k d ha hd)) :
    companionValue P (fullFamily P D) q = IntegralMixedFullHistoryCompanionBits.value P D q := by
  unfold companionValue PaddedIntegralGeneratorFinBits.Family.value
  rw [matrix_creating P D q r k d ha hd hc]
  rfl

end LeanCanny.Algebra.IntegralMixedNormalizedCompanionBits
