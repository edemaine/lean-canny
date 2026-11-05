/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoefficientMarkedRecordEffectiveCutoff
public import LeanCanny.Encoding.IntegralMixedRoadmapVertexBudget

/-! # One original cutoff for every bounded structural record table

The original word allowance covers all candidate labels, padded record tables
and seed/probe choices. No sampler word is chosen when forming the cutoff.
This controls normalization of the recursive interpreter; graph query signs
and edge transport require their own bounds.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordUniformCutoff
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapRecordChain IntegralMixedRoadmapWidth
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → Term} (hn : UnaryFn n)
  (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

theorem exists_cutoff : ∃ C : List Bool → ℕ, BinaryFn C ∧
    ∀ original ctx, ctx.length ≤ contextBudget hn ht ha original →
      CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ C original :=
  (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha).wordEnvelope
    (contextBudget_unary hn ht ha)

noncomputable def cutoff : List Bool → ℕ := Classical.choose (exists_cutoff hn ht ha)

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) :=
  (Classical.choose_spec (exists_cutoff hn ht ha)).1

theorem effectiveCutoff_le (original ctx : List Bool)
    (hctx : ctx.length ≤ contextBudget hn ht ha original) :
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ cutoff hn ht ha original :=
  (Classical.choose_spec (exists_cutoff hn ht ha)).2 original ctx hctx

theorem padded_cutoff_le (original label : List Bool)
    (hlabel : label.length ≤ IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)
    {labels : ℕ} (records : Records (dimension (n := n) original) (recordBudget hn ht ha original) labels)
    (seed probe : Word (recordBudget hn ht ha original)) :
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (records.root seed probe (pair original label) []) ≤ cutoff hn ht ha original := by
  apply effectiveCutoff_le hn ht ha original
  have H := padded_context_length hn ht ha original label hlabel records seed probe
  rw [pair_length, List.length_nil, Nat.add_zero] at H
  omega

/-- A single original cutoff works for every prefix of every padded table. -/
theorem specializes_padded (original label : List Bool)
    (hlabel : label.length ≤ IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)
    {labels : ℕ} (records : Records (dimension (n := n) original) (recordBudget hn ht ha original) labels)
    (seed probe : Word (recordBudget hn ht ha original)) (radius : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count (records.root seed probe (pair original label) []))
    (hR : cutoff hn ht ha original ≤ radius (records.root seed probe (pair original label) [])) :
    let ctx := records.root seed probe (pair original label) []
    CoefficientHistoryPrefix.Specializes (radius ctx)
      (CoefficientMarkedRecordPrefix.build hn ht ha ctx (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
        (CoefficientMarkedRecordActual.codes ctx k))
      (CoefficientMarkedRecordNative.run hn ht ha ctx radius (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
        (CoefficientMarkedRecordActual.codes ctx k) (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk)) := by
  exact CoefficientMarkedRecordEffectiveCutoff.specializes_above_effective hn ht ha _ radius k hk
    ((padded_cutoff_le hn ht ha original label hlabel records seed probe).trans hR)

noncomputable def contextTopHeight (ctx : List Bool) : ℕ :=
  IntegerPolynomialDyadic.massBudget
    (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx)

theorem contextTopHeight_binary : BinaryFn (contextTopHeight hn ht ha) :=
  IntegerPolynomialDyadic.massBudget_binary
    (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope_binary hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset_binary hn ht ha)

theorem exists_topHeight : ∃ H : List Bool → ℕ, BinaryFn H ∧
    ∀ original ctx, ctx.length ≤ contextBudget hn ht ha original → contextTopHeight hn ht ha ctx ≤ H original :=
  (contextTopHeight_binary hn ht ha).wordEnvelope (contextBudget_unary hn ht ha)

noncomputable def topHeight : List Bool → ℕ := Classical.choose (exists_topHeight hn ht ha)

theorem topHeight_binary : BinaryFn (topHeight hn ht ha) :=
  (Classical.choose_spec (exists_topHeight hn ht ha)).1

/-- All next-cut parameter matrices share one original coefficient-mass exponent. -/
theorem topEntryBound (original ctx : List Bool)
    (hctx : ctx.length ≤ contextBudget hn ht ha original) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false) :
    CoefficientMarkedRecordSpecialization.topEntryBound hn ht ha ctx
      (CoefficientMarkedRecordPrefix.build hn ht ha ctx (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
        (CoefficientMarkedRecordActual.codes ctx k)) (IntegralMixedCausalRecordPlanBits.code ctx k)
      (topHeight hn ht ha original) := by
  have HE := CoefficientMarkedRecordCoefficientBounds.topEntryBound_of_cutoff_le hn ht ha ctx k hk hc
    (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx)
    (CoefficientMarkedRecordEffectiveCutoff.cutoff_le_effective hn ht ha ctx k hk.le)
  have HH := (Classical.choose_spec (exists_topHeight hn ht ha)).2 original ctx hctx
  intro i j
  exact (HE i j).trans (Nat.pow_le_pow_right (by decide) HH)

end LeanCanny.Encoding.CoefficientMarkedRecordUniformCutoff
