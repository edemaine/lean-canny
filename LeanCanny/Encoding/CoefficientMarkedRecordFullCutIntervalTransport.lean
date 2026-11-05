/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutCoefficientGuards
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutOrderSign
public import LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientInterval
/-! # The complete literal coefficient-only NoBad interval predicate on one curve -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutIntervalTransport
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def cutoff (ctx : List Bool) := CoefficientMarkedRecordFullCutComparison.cutoff hn ht ha ctx+
  CoefficientMarkedRecordFullCutOrderSign.cutoff hn ht ha ctx+CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx+1

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) :=
  (((CoefficientMarkedRecordFullCutComparison.cutoff_binary hn ht ha).add
    (CoefficientMarkedRecordFullCutOrderSign.cutoff_binary hn ht ha)).add
    (CoefficientMarkedRecordFullCutSign.cutoff_binary hn ht ha)).add (BinaryFn.const 1)

theorem comparison_cutoff_le (ctx : List Bool) : CoefficientMarkedRecordFullCutComparison.cutoff hn ht ha ctx ≤ cutoff hn ht ha ctx := by
  unfold cutoff
  omega
theorem order_cutoff_le (ctx : List Bool) : CoefficientMarkedRecordFullCutOrderSign.cutoff hn ht ha ctx ≤ cutoff hn ht ha ctx := by
  unfold cutoff
  omega
theorem coefficient_cutoff_le (ctx : List Bool) : CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx ≤ cutoff hn ht ha ctx := by
  unfold cutoff
  omega

variable {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
local notation "CTX" => CoefficientMarkedRecordFullCutInstalled.context (n := n)

/-- All native conjuncts are derived: PMV comparison, OWN validity, every
range/stage check, every finite coefficient guard and strict numerical order.
Non-cut records are rejected by the literal Bounds predicate at both radii. -/
theorem language_on_curve (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (left right : ℕ) (hRc : cutoff hn ht ha ctx ≤ R ctx) (hSc : cutoff hn ht ha ctx ≤ S ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R ctx) (hv : v.val = (2 : ℝ)^S ctx) (wR wS : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) wR)
    (hwS : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (CTX ctx k left right) wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (CTX ctx k left right) wS hwS).val (x v)) :
    pair (CTX ctx k left right) wR ∈ IntegralMixedPhysicalCutCoefficientInterval.language hn ht ha hR false ↔
      pair (CTX ctx k left right) wS ∈ IntegralMixedPhysicalCutCoefficientInterval.language hn ht ha hS false := by
  have HB := (CoefficientMarkedRecordFullCutCoefficientGuards.bounds_iff hn ht ha hR ctx wR k left right hk).trans
    (CoefficientMarkedRecordFullCutCoefficientGuards.bounds_iff hn ht ha hS ctx wS k left right hk).symm
  by_cases hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false
  · have hcStart := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (comparison_cutoff_le hn ht ha ctx)).trans ha0
    have hoStart := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (order_cutoff_le hn ht ha ctx)).trans ha0
    have hgStart := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (coefficient_cutoff_le hn ht ha ctx)).trans ha0
    have HC := CoefficientMarkedRecordFullCutComparison.comparison_on_curve hn ht ha hR ctx k hk hc left right hS
      ((comparison_cutoff_le hn ht ha ctx).trans hRc) ((comparison_cutoff_le hn ht ha ctx).trans hSc)
      hcStart x hx u v hu hv wR wS hwR hwS hjR hjS
    have HO := CoefficientMarkedRecordFullCutOrderSign.value_on_curve hn ht ha hR hS ctx k left right
      ((order_cutoff_le hn ht ha ctx).trans hRc) ((order_cutoff_le hn ht ha ctx).trans hSc)
      hoStart x hx u v hu hv wR wS hwR hwS hjR hjS
    have HG := CoefficientMarkedRecordFullCutCoefficientGuards.guards_on_curve hn ht ha hR hS ctx
      ((coefficient_cutoff_le hn ht ha ctx).trans hRc) ((coefficient_cutoff_le hn ht ha ctx).trans hSc)
      hgStart x hx u v hu hv k left right hk hc wR wS hwR hwS hjR hjS
    simp only [IntegralMixedPhysicalCutCoefficientInterval.language, Set.mem_ofPred_eq,
      pairFst_pair, pairSnd_pair, hwR, hwS, true_and]
    exact and_congr HC (and_congr HB (and_congr HG (Iff.of_eq (congrArg (fun z => z = InfinitesimalSign.encode 1) HO))))
  · have HBR : ¬IntegralMixedPhysicalCutOpenInterval.Bounds hn ht ha hR false (pair (CTX ctx k left right) wR) := by
      rw [CoefficientMarkedRecordFullCutCoefficientGuards.bounds_iff hn ht ha hR ctx wR k left right hk]
      exact fun h => hc h.2.2.2
    have HBS := mt HB.mpr HBR
    simp only [IntegralMixedPhysicalCutCoefficientInterval.language, Set.mem_ofPred_eq,
      HBR, HBS, and_false, false_and]

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutIntervalTransport
