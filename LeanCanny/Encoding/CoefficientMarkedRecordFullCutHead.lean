/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientFullCutHeadQueries
public import LeanCanny.Encoding.CoefficientMarkedRecordChoiceFactor
/-! # The stored relative factor at an actual raw prefix is a constructed family -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutHead
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open IntegralMixedRelativeCuts CoefficientFullCutHeadQueries
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem atChoice_of_le {a : ℕ} {P : SpatialSource a} (r : IntegralMixedCriticalSweep.Rule a)
    (c : Kind P r) (N : ℕ) (h : choiceIndex r c ≤ N) : atChoice r c N = c := by
  cases c <;> simp only [choiceIndex] at h <;> simp [atChoice, min_eq_right h]

noncomputable def selectedPolynomial (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) : Polynomial (MvPolynomial (Fin ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth key)) ℤ) :=
  let G := IntegralMixedFramedHistoryFamilyBits.family P D H
  (G.state key).sampler.scalarPrefix.basis.polynomial
    (IntegralMixedRelativeCuts.factor (G.state key) (G.birth_bound key) (G.rule key) (G.kind key))

theorem selectedPolynomial_planned (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (key : List Bool) :
    HEq (selectedPolynomial (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key) (selectedPolynomial P D H key) := by
  apply heq_of_eq
  dsimp only [selectedPolynomial, IntegralMixedFramedHistoryFamilyBits.family]
  rw [IntegralMixedFramedCutPlanning.selection P D H L F C key]
  rfl

private theorem saturated_factor (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) :
    let G := IntegralMixedFramedHistoryFamilyBits.family P D H
    CoefficientMarkedRecordChoiceFactor.nativeFactors (G.state key) (G.birth_bound key)
      (CoefficientMarkedRecordCutSelection.familySelection G key) (2^G.width key) = selectedPolynomial P D H key := by
  dsimp only
  let G := IntegralMixedFramedHistoryFamilyBits.family P D H
  have HC : choiceIndex (G.rule key) (G.kind key) ≤ 2^G.width key := by
    have HE : choiceIndex (G.rule key) (G.kind key) = IntegralMixedRawKindBits.choice G key := by
      cases h : G.kind key <;> simp only [choiceIndex, IntegralMixedRawKindBits.choice, h]
    rw [HE]
    exact (IntegralMixedRawKindBits.choice_le G key).trans (G.scalar_cap key)
  dsimp only [CoefficientMarkedRecordChoiceFactor.nativeFactors,
    CoefficientMarkedRecordCutSelection.familySelection, selectedPolynomial]
  rw [atChoice_of_le _ _ _ HC]

private theorem polynomial_at_heq {m k : ℕ}
    (p : ℕ → Polynomial (MvPolynomial (Fin m) ℤ)) (q : ℕ → Polynomial (MvPolynomial (Fin k) ℤ))
    (hm : m = k) (hp : HEq p q) (i : ℕ) : HEq (p i) (q i) := by
  cases hm
  cases eq_of_heq hp
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def polynomial (ctx : List Bool) (k : ℕ) :=
  CoefficientMarkedRecordChoiceFactor.polynomial hn ht ha ctx k (2^CoefficientMarkedIntegerBirth.width hn ht ha ctx)

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed CoefficientMarkedRecordPrefix.build CoefficientMarkedRecordNative.run
  selectedPolynomial CoefficientMarkedRecordChoiceFactor.nativeFactors CoefficientMarkedRecordChoiceFactor.polynomial

theorem polynomial_specializes (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (aux : List Bool) (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    HEq ((polynomial hn ht ha ctx k).map (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))))
      (selectedPolynomial (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
        (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)) := by
  have HM := CoefficientMarkedRecordChoiceFactor.specializes_family hn ht ha ctx R k hk hc aux hR
  have HB := CoefficientMarkedRecordRows.family_birth hn ht ha ctx R k hk.le aux
  have HS := saturated_factor (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
    (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)
  dsimp only at HS
  let G := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R
  let key := CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux
  let F := CoefficientMarkedRecordChoiceFactor.nativeFactors (G.state key) (G.birth_bound key)
    (CoefficientMarkedRecordCutSelection.familySelection G key)
  have HN := congrArg (fun b => 2^b) (CoefficientMarkedRecordRows.family_width hn ht ha ctx R k aux)
  have HS' := (congrArg F HN).trans HS
  unfold polynomial
  exact (polynomial_at_heq _ _ HB HM (2^CoefficientMarkedIntegerBirth.width hn ht ha ctx)).trans (heq_of_eq HS')

theorem polynomial_specializes_certified (ctx : List Bool) {R : List Bool → ℕ} (hR : BinaryFn R) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (aux : List Bool) (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    HEq ((polynomial hn ht ha ctx k).map (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))))
      (selectedPolynomial (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
        (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)) := by
  have HS := selectedPolynomial_planned (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
    (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)
  have HP := HS.symm
  exact (polynomial_specializes hn ht ha ctx R k hk hc aux hlarge).trans HP

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutHead
