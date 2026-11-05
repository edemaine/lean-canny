/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordChoicePhysicalBounds
public import LeanCanny.Encoding.CoefficientMarkedRecordTermDegree
public import LeanCanny.Encoding.CoefficientMarkedRecordFullHeadControls
/-! # Finite spatial support of actual clipped physical cut probes -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordChoicePhysical
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedFramedPhysicalLayoutCongruence
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem query_degree {R : Type*} [CommRing R] {m : ℕ}
    (column : Fin m → ℕ) (w : Fin m → ℕ) (p : Polynomial (MvPolynomial (Fin m) R))
    (tau W : ℕ) (hw : ∀ i, w i ≤ W) : (query column w p tau).totalDegree ≤ W * (p.coeff tau).totalDegree :=
  (MvPolynomial.totalDegree_rename_le _ _).trans (CoordinatePowerSubstitution.degree_le _ _ _ hw)

private theorem query_variables {R : Type*} [CommRing R] {m N : ℕ}
    (column : Fin m → Fin N) (w : Fin m → ℕ) (p : Polynomial (MvPolynomial (Fin m) R)) (tau : ℕ) :
    (query (fun i => (column i).val) w p tau).vars ⊆ Finset.range N := by
  intro j hj
  obtain ⟨i, _, rfl⟩ := MvPolynomial.mem_vars_rename (fun i => (column i).val) _ hj
  exact Finset.mem_range.mpr (column i).isLt

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def spatialDegree (ctx : List Bool) :=
  CoefficientMarkedRecordTermQuery.spatialPowerBound hn ht ha ctx *
    CoefficientMarkedRecordCutCoefficientBounds.scalarDegree hn ht ha ctx

theorem spatialDegree_binary : BinaryFn (spatialDegree hn ht ha) :=
  (CoefficientMarkedRecordTermQuery.spatialPowerBound_binary hn ht ha).mul
    (CoefficientMarkedRecordCutCoefficientBounds.scalarDegree_binary hn ht ha)

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build

/-- All alternative native choices and all target coefficients have the
same original spatial box, including coefficients beyond the stored cut degree. -/
theorem spatial_degree (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (requested tau : ℕ) :
    (polynomial hn ht ha ctx k hk requested tau).totalDegree ≤ spatialDegree hn ht ha ctx := by
  unfold polynomial
  apply (query_degree _ _ _ tau (CoefficientMarkedRecordTermQuery.spatialPowerBound hn ht ha ctx) ?_).trans
    (Nat.mul_le_mul_left _ (CoefficientMarkedRecordChoiceFactor.scalar_degree hn ht ha ctx k hk requested tau))
  intro i
  exact (UniformIntegralPowerSchedule.weights_le _ _ _ i).trans
    (UniformIntegralPowerSchedule.birth_le _ _ _ ((Nat.sub_le _ _).trans
      (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk)))

/-- This support bound uses the actual full prefix physical columns;
it is independent of a monomial total-degree estimate. -/
theorem variable_box (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (requested tau : ℕ) :
    (polynomial hn ht ha ctx k hk requested tau).vars ⊆
      Finset.range (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count := by
  exact query_variables
    ((CoefficientMarkedRecordRowLayout.fixed hn ht ha ctx k hk).enumeration ∘
      (CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k).scalar)
    _ _ tau

/-- The original Unary count reader is shared with the complete-row heads. -/
theorem count_unary : UnaryFn (CoefficientMarkedRecordFullHeadControls.count hn ht ha) :=
  CoefficientMarkedRecordFullHeadControls.count_unary hn ht ha

end LeanCanny.Encoding.CoefficientMarkedRecordChoicePhysical
