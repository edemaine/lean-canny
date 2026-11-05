/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTermRecipe
public import LeanCanny.Encoding.CoefficientMarkedRecordLeafNative
public import LeanCanny.Encoding.CoefficientMarkedRecordTermDegree
/-! # Actual certified term queries specialize from the original full prefix -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTermNative
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem map_arguments (φ : ℤ[X] →+* ℤ) (A : CoefficientBankTermQuery.Arguments ℤ[X])
    (B : CoefficientBankTermQuery.Arguments ℤ) (hA : A.map φ = B) (p : LeanCanny.ETR.Term) :
    HEq (MvPolynomial.map φ (CoefficientBankTermQuery.polynomial A p))
      (CoefficientBankTermQuery.polynomial B p) := by
  rw [CoefficientBankTermQuery.polynomial_map]
  exact CoefficientBankTermQuery.polynomial_heq_of_eq _ _ hA p

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build

/-- Both the physical arguments and the decoded term are the literal ones
at the same original root, before any tuple is sampled. -/
theorem polynomial_actual (word : List Bool → List Bool) (ctx : List Bool) :
    HEq (CoefficientMarkedRecordTermRecipe.polynomial (B) word (IntegralMixedPhysicalMarkedTest.sampleContext ctx))
      (CoefficientBankTermQuery.polynomial
        (CoefficientMarkedRecordLeafQuery.nativeArguments hn ht ha ctx R (IntegralMixedCausalRecordPlanBits.count ctx) [])
        (CoefficientMarkedRecordTermQuery.termSyntax word ctx)) := by
  have hs : (IntegralMixedFramedBankTermBits.source word).syntax
      ((B).key (IntegralMixedPhysicalMarkedTest.sampleContext ctx)) = CoefficientMarkedRecordTermQuery.termSyntax word ctx := by
    change LeanCanny.ETR.TermView.term (word (pairFst ((B).key (pair ctx [])))) = _
    rw [IntegralMixedPhysicalMarkedPlan.key_root hn ht ha hR false ctx]
    rfl
  unfold CoefficientMarkedRecordTermRecipe.polynomial
  rw [hs]
  exact CoefficientBankTermQuery.polynomial_heq_of_eq _ _
    (CoefficientMarkedRecordLeafNative.arguments_actual hn ht ha hR ctx) _

/-- The actual native query, including the full creating powers and common
clearing denominator, is the original symbolic coefficient specialization. -/
theorem specializes (word : List Bool → List Bool) (ctx : List Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    HEq (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))
      (CoefficientMarkedRecordTermQuery.polynomial hn ht ha word ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl))
      (CoefficientMarkedRecordTermRecipe.polynomial (B) word (IntegralMixedPhysicalMarkedTest.sampleContext ctx)) := by
  have hargs := CoefficientMarkedRecordTermQuery.arguments_specialize hn ht ha ctx R
    (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] hlarge
  have he := map_arguments (evalRingHom ((2 : ℤ)^R ctx)) _ _ hargs (CoefficientMarkedRecordTermQuery.termSyntax word ctx)
  exact he.trans (polynomial_actual hn ht ha hR word ctx).symm

end LeanCanny.Encoding.CoefficientMarkedRecordTermNative
