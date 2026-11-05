/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientBankTermDegree
public import LeanCanny.Encoding.CoefficientMarkedRecordTermBounds
/-! # One original spatial box for all actual prefix term queries -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTermQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem degreeBound_pack {R : Type*} [CommRing R] (S W : ℕ)
    (D : CoefficientMarkedRecordRows.Data R) (q : R) (c : ℕ → R) (p : LeanCanny.ETR.Term) :
    CoefficientBankTermDegree.degreeBound (pack S W D q c) p =
      p.toData.size * (2 * p.toData.size) * UniformIntegralPowerSchedule.birth S (2 ^ W) S := rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def spatialPowerBound (ctx : List Bool) :=
  UniformIntegralPowerSchedule.birth (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
    (2 ^ CoefficientMarkedIntegerBirth.width hn ht ha ctx)
    (CoefficientMarkedRecordActual.horizon hn ht ha ctx)

noncomputable def spatialDegree (word : List Bool → List Bool) (ctx : List Bool) :=
  termSize word ctx * (2 * termSize word ctx) * spatialPowerBound hn ht ha ctx

theorem spatialPowerBound_binary : BinaryFn (spatialPowerBound hn ht ha) := by
  have HS : UnaryFn (CoefficientMarkedRecordActual.horizon hn ht ha) :=
    (IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).cap.add (UnaryFn.const 1)
  have HN : BinaryFn (fun ctx => 2 ^ CoefficientMarkedIntegerBirth.width hn ht ha ctx) :=
    (BinaryFn.const 2).powUnary (IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).width
  exact UniformIntegralPowerSchedule.birth_binary HS HN HS

theorem spatialDegree_binary (word : List Bool → List Bool) (hw : word ∈ FP) :
    BinaryFn (spatialDegree hn ht ha word) :=
  ((BinaryFn.ofUnary (termSize_unary word hw)).mul
    ((BinaryFn.const 2).mul (BinaryFn.ofUnary (termSize_unary word hw)))).mul
      (spatialPowerBound_binary hn ht ha)

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build

private theorem arguments_birth_bound (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) :
    (arguments hn ht ha ctx k hk).birth ≤ (arguments hn ht ha ctx k hk).horizon := by
  unfold arguments pack CoefficientMarkedRecordRows.symbolic CoefficientMarkedRecordRows.prefixData
  change (CoefficientMarkedPreludeActual.indices n ctx).length +
    (CoefficientMarkedRecordActual.codes ctx k).length ≤ CoefficientMarkedRecordActual.horizon hn ht ha ctx
  rw [CoefficientMarkedRecordActual.codes_length]
  exact CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk

private theorem arguments_degreeBound (word : List Bool → List Bool) (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) :
    CoefficientBankTermDegree.degreeBound (arguments hn ht ha ctx k hk) (termSyntax word ctx) =
      spatialDegree hn ht ha word ctx := by
  unfold arguments
  rw [degreeBound_pack]
  rfl

attribute [local irreducible] arguments pack CoefficientBankTermQuery.polynomial

/-- The spatial-degree bound is independent of the prefix, AUX and radius;
all powers and the term's indexed clearing recipe remain the native ones. -/
theorem polynomial_spatial_degree (word : List Bool → List Bool) (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) :
    (polynomial hn ht ha word ctx k hk).totalDegree ≤ spatialDegree hn ht ha word ctx := by
  unfold polynomial
  apply (CoefficientBankTermDegree.degree _ _ (arguments_birth_bound hn ht ha ctx k hk)).trans_eq
  exact arguments_degreeBound hn ht ha word ctx k hk

end LeanCanny.Encoding.CoefficientMarkedRecordTermQuery
