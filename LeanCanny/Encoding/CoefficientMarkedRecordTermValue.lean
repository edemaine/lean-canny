/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTermNative
public import LeanCanny.Encoding.CoefficientMarkedRecordTermSign
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullSemantics
/-! # Literal native term readers at their own complete full tuple -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTermValue
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem evaluate_heq {N M : ℕ} (hn : N = M) (p : MvPolynomial (Fin N) ℤ)
    (q : MvPolynomial (Fin M) ℤ) (hp : HEq p q) (z : Fin N → ℝ) (w : Fin M → ℝ) (hz : HEq z w) :
    p.eval₂ (Int.castRingHom ℝ) z = q.eval₂ (Int.castRingHom ℝ) w := by
  cases hn
  cases eq_of_heq hp
  cases eq_of_heq hz
  rfl

private theorem evaluate_map {N : ℕ} (r : ℕ) (p : MvPolynomial (Fin N) ℤ[X]) (z : Fin N → ℝ) :
    (MvPolynomial.map (evalRingHom ((2 : ℤ)^r)) p).eval₂ (Int.castRingHom ℝ) z =
      p.eval₂ (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^r)) z := by
  rw [MvPolynomial.eval₂_map]
  have h : (Int.castRingHom ℝ).comp (evalRingHom ((2 : ℤ)^r)) =
      SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^r) := by
    apply Polynomial.ringHom_ext
    · intro a; simp [SymbolicScaledSquarefree.scalarEvaluation]
    · simp [SymbolicScaledSquarefree.scalarEvaluation]
  rw [h]

private theorem arguments_dimension (B : IntegralFramedBankQuery.Bank) (c : List Bool) :
    (CoefficientMarkedRecordLeafRecipe.arguments B c).dimension = (IntegralFramedPhysicalBankTerm.input B).count c := rfl

private noncomputable def tuple (B : IntegralFramedBankQuery.Bank) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w) :
    Fin (CoefficientMarkedRecordLeafRecipe.arguments B c).dimension → ℝ :=
  (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hw).val

private theorem tuple_heq (B : IntegralFramedBankQuery.Bank) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    {N : ℕ} (z : Fin N → ℝ)
    (hz : HEq (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hw).val z) :
    HEq (tuple B c w hw) z := hz

private theorem native_recipe (B : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (word : List Bool → List Bool) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w) :
    CoefficientMarkedRecordTermRecipe.reader B T hr word c w = InfinitesimalSign.encode (SignType.sign
      ((CoefficientMarkedRecordTermRecipe.polynomial B word c).eval₂ (Int.castRingHom ℝ) (tuple B c w hw))) :=
  CoefficientMarkedRecordTermRecipe.value B T hr word c w hw

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false

noncomputable def value (word : List Bool → List Bool) (ctx w : List Bool) :=
  CoefficientMarkedRecordTermRecipe.reader (B) (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR false) word (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

theorem value_eq (word : List Bool → List Bool) (ctx w : List Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w)
    (z : Fin (CoefficientMarkedRecordTermSign.count hn ht ha ctx) → ℝ)
    (hz : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw).val z) :
    value hn ht ha hR word ctx w = InfinitesimalSign.encode (SignType.sign
      ((CoefficientMarkedRecordTermSign.polynomial hn ht ha word ctx).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R ctx)) z)) := by
  have hv := native_recipe (B) (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR false) word
    (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw
  have hs := CoefficientMarkedRecordTermNative.specializes hn ht ha hR word ctx hlarge
  have hdim : CoefficientMarkedRecordTermSign.count hn ht ha ctx =
      (CoefficientMarkedRecordLeafRecipe.arguments (B) (IntegralMixedPhysicalMarkedTest.sampleContext ctx)).dimension :=
    (CoefficientMarkedRecordCriticalFullSemantics.full_count hn ht ha hR ctx).trans
      (arguments_dimension (B) (IntegralMixedPhysicalMarkedTest.sampleContext ctx)).symm
  have he := @evaluate_heq (CoefficientMarkedRecordTermSign.count hn ht ha ctx)
    (CoefficientMarkedRecordLeafRecipe.arguments (B) (IntegralMixedPhysicalMarkedTest.sampleContext ctx)).dimension hdim
    (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx)) (CoefficientMarkedRecordTermSign.polynomial hn ht ha word ctx))
    (CoefficientMarkedRecordTermRecipe.polynomial (B) word (IntegralMixedPhysicalMarkedTest.sampleContext ctx)) hs z
    (tuple (B) (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw)
    (tuple_heq (B) (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw z hz).symm
  have hm := evaluate_map (R ctx) (CoefficientMarkedRecordTermSign.polynomial hn ht ha word ctx) z
  exact hv.trans (congrArg (fun v : ℝ => InfinitesimalSign.encode (SignType.sign v)) (he.symm.trans hm))

end LeanCanny.Encoding.CoefficientMarkedRecordTermValue
