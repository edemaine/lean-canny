/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTermValue
/-! # Actual native bank-term signs on one complete root branch -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTermTransport
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem effective_le (word : List Bool → List Bool) (ctx : List Bool) :
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤
      CoefficientMarkedRecordTermSign.cutoff hn ht ha word ctx :=
  (CoefficientMarkedRecordCartesianRows.effectiveCutoff_le hn ht ha ctx).trans
    (CoefficientMarkedRecordTermSign.row_cutoff_le hn ht ha word ctx)

theorem value_on_curve (word : List Bool → List Bool) (ctx : List Bool) {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
    (hRlarge : CoefficientMarkedRecordTermSign.cutoff hn ht ha word ctx ≤ R ctx)
    (hSlarge : CoefficientMarkedRecordTermSign.cutoff hn ht ha word ctx ≤ S ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordTermSign.cutoff hn ht ha word ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordTermSign.count hn ht ha ctx) → ℝ))
    (hx : ∀ y : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl y.val (x y))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R ctx) (hv : v.val = (2 : ℝ)^S ctx)
    (w w' : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w)
    (hw' : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w')
    (hz : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw).val (x u))
    (hz' : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w' hw').val (x v)) :
    CoefficientMarkedRecordTermValue.value hn ht ha hR word ctx w =
      CoefficientMarkedRecordTermValue.value hn ht ha hS word ctx w' := by
  rw [CoefficientMarkedRecordTermValue.value_eq hn ht ha hR word ctx w
      ((effective_le hn ht ha word ctx).trans hRlarge) hw (x u) hz,
    CoefficientMarkedRecordTermValue.value_eq hn ht ha hS word ctx w'
      ((effective_le hn ht ha word ctx).trans hSlarge) hw' (x v) hz']
  have h := CoefficientMarkedRecordTermSign.sign_on_root_curve hn ht ha word ctx ha0 x hx u v
  rw [hu, hv] at h
  exact congrArg InfinitesimalSign.encode h

end LeanCanny.Encoding.CoefficientMarkedRecordTermTransport
