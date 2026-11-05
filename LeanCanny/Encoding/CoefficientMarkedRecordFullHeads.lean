/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.AffineRingCoordinateMap
public import LeanCanny.Algebra.AffineRingGramBounds
public import LeanCanny.Encoding.CoefficientMarkedRecordRowBounds
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalMetadata
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalDegree
/-! # Constructed complete heads for every actual full physical raw column

The original advertised row degrees are computed from the literal header
table. Scalar, multiplier and physical columns all use the same complete
affine Gram construction as the native full sampler.
-/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullHeads
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open CoefficientMarkedRecordRows
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def heads {R : Type*} [CommRing R] (D : CoefficientMarkedRecordRows.Data R) (d : ℕ → ℕ) :=
  fun i : Fin D.count => AffineRingCoordinates.annihilator D.rows (fun j => d j.val) i

private theorem heads_map {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (D : CoefficientMarkedRecordRows.Data R) (d : ℕ → ℕ) :
    (fun i => (heads D d i).map φ) = heads (CoefficientMarkedRecordRows.map φ D) d := by
  funext i
  exact AffineRingCoordinateMap.annihilator φ D.rows (fun j => d j.val) i

private theorem heads_congr (D E : CoefficientMarkedRecordRows.Data ℤ) (he : D = E)
    (d e : ℕ → ℕ) (hd : d = e) : HEq (heads D d) (heads E e) := by
  cases he
  cases hd
  rfl

private theorem degree_planned (P : IntegralCriticalHistoryTask.Parameters)
    (T : IntegralMixedHeaderTablesBits.Tables) (L F C : List Bool → ℕ) (q : List Bool) :
    IntegralMixedFramedPhysicalRowDegree.degree (IntegralMixedFramedNormalizationBits.planned P L F C) T q =
      IntegralMixedFramedPhysicalRowDegree.degree P T q := rfl

noncomputable def samplerAnnihilators (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) :=
  fun i : Fin (IntegralFramedPhysicalSquare.count P D key) =>
    AffineFiniteCoordinates.annihilator (IntegralFramedPhysicalSquare.sampler P D H key).rows
      (IntegralFramedPhysicalSquare.sampler P D H key).degrees i

private theorem sampler_heads (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
    (key : List Bool) :
    HEq (heads (CoefficientMarkedRecordRowBounds.samplerData P D H key)
      (fun j => IntegralMixedFramedPhysicalRowDegree.degree P T (pair key (BinaryNatCode.encode j))))
      (samplerAnnihilators P D H key) := by
  apply heq_of_eq
  have hd : (fun i : Fin (IntegralFramedPhysicalSquare.count P D key) =>
      IntegralMixedFramedPhysicalRowDegree.degree P T (pair key (BinaryNatCode.encode i.val))) =
      (IntegralFramedPhysicalSquare.sampler P D H key).degrees := by
    funext i
    exact IntegralMixedFramedPhysicalDegree.degree_eq P D H T hr key i
  change (fun i => AffineRingCoordinates.annihilator (IntegralFramedPhysicalSquare.sampler P D H key).rows
    (fun j => IntegralMixedFramedPhysicalRowDegree.degree P T (pair key (BinaryNatCode.encode j.val))) i) = _
  rw [hd]
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def degrees (ctx : List Bool) (k : ℕ) (aux : List Bool) (j : ℕ) :=
  IntegralMixedFramedPhysicalRowDegree.degree (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha)
    (pair (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux) (BinaryNatCode.encode j))

noncomputable def nativeDegrees (ctx : List Bool) {R : List Bool → ℕ} (hR : BinaryFn R)
    (k : ℕ) (aux : List Bool) (j : ℕ) :=
  IntegralMixedFramedPhysicalRowDegree.degree (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
    (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
    (pair (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux) (BinaryNatCode.encode j))

theorem degrees_eq (ctx : List Bool) {R : List Bool → ℕ} (hR : BinaryFn R) (k : ℕ) (aux : List Bool) :
    degrees hn ht ha ctx k aux = nativeDegrees hn ht ha ctx hR k aux := by
  funext j
  unfold degrees nativeDegrees
  rw [CoefficientMarkedRecordCriticalMetadata.tables_eq hn ht ha hR]
  exact (degree_planned (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha) (fun _ => 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) _).symm

noncomputable def polynomial (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool) :=
  heads (symbolic hn ht ha ctx k hk) (degrees hn ht ha ctx k aux)

noncomputable def native (ctx : List Bool) {R : List Bool → ℕ} (hR : BinaryFn R) (k : ℕ) (aux : List Bool) :=
  heads (CoefficientMarkedRecordRowBounds.certifiedIndexed hn ht ha ctx hR k aux)
    (nativeDegrees hn ht ha ctx hR k aux)

attribute [local irreducible] polynomial native degrees nativeDegrees heads samplerAnnihilators
  CoefficientMarkedRecordRowBounds.samplerData IntegralMixedSourceIntegerRecordAppend.plan
  IntegralMixedFramedHistoryFamilyBits.family

theorem specializes (ctx : List Bool) {R : List Bool → ℕ} (hR : BinaryFn R) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    HEq (fun i => (polynomial hn ht ha ctx k hk aux i).map (evalRingHom ((2 : ℤ)^R ctx)))
      (native hn ht ha ctx hR k aux) := by
  have hm := heads_map (evalRingHom ((2 : ℤ)^R ctx)) (symbolic hn ht ha ctx k hk) (degrees hn ht ha ctx k aux)
  have he := heads_congr _ _ (CoefficientMarkedRecordRowBounds.map_certified hn ht ha ctx hR k hk aux hlarge)
    _ _ (degrees_eq hn ht ha ctx hR k aux)
  unfold polynomial native
  exact (heq_of_eq hm).trans he

/-- The specialized heads are literally those used by complete native sampling. -/
theorem native_eq (ctx : List Bool) {R : List Bool → ℕ} (hR : BinaryFn R) (k : ℕ) (aux : List Bool) :
    HEq (native hn ht ha ctx hR k aux)
      (samplerAnnihilators (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
        (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)) := by
  have hh := sampler_heads
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
    (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR false)
    (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)
  unfold native nativeDegrees CoefficientMarkedRecordRowBounds.certifiedIndexed
  exact hh

end LeanCanny.Encoding.CoefficientMarkedRecordFullHeads
