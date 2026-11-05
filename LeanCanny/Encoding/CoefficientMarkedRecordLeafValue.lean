/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordLeafNative
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullSemantics
/-! # Native original leaf signs at the same complete full tuple -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordLeafValue
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

private theorem native_recipe (B : IntegralFramedBankQuery.Bank) (Q : IntegerPolynomialRootQueriesBits.Source)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    (i : ℕ) (hi : i < (family B.parameters B.plan B.data).birth (B.key c)) :
    CoefficientMarkedRecordLeafRecipe.reader B Q c w i = InfinitesimalSign.encode (SignType.sign
      ((CoefficientBankLeafQuery.polynomial (CoefficientMarkedRecordLeafRecipe.arguments B c)
        (Q.polynomial (pair c (BinaryNatCode.encode i))) (2*Q.degree (pair c (BinaryNatCode.encode i))) i).eval₂
        (Int.castRingHom ℝ) (tuple B c w hw))) :=
  CoefficientMarkedRecordLeafRecipe.value B Q c w hw i hi

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false

noncomputable def value (ctx w : List Bool) (i : ℕ) :=
  CoefficientMarkedRecordLeafRecipe.reader (B) (IntegralMixedPhysicalMarkedPlan.leafSource hn ht ha (R := R) false)
    (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w i

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

theorem value_eq (ctx w : List Bool) (i : CoefficientMarkedRecordLeafSign.Label (n := n) ctx)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w)
    (z : Fin (CoefficientMarkedRecordLeafSign.count hn ht ha ctx) → ℝ)
    (hz : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw).val z) :
    value hn ht ha hR ctx w i.val = InfinitesimalSign.encode (SignType.sign
      ((CoefficientMarkedRecordLeafSign.polynomial hn ht ha ctx i).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R ctx)) z)) := by
  have hk := CoefficientMarkedRecordTraceProbeNative.terminal hn ht ha hR (IntegralMixedPhysicalMarkedTest.sampleContext ctx)
  simp only [IntegralMixedPhysicalMarkedTest.sampleContext, pairFst_pair] at hk
  have hb : (family (B).parameters (B).plan (B).data).birth
      ((B).key (IntegralMixedPhysicalMarkedTest.sampleContext ctx)) =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx := by
    simp only [IntegralMixedPhysicalMarkedTest.sampleContext]
    rw [hk]
    exact CoefficientMarkedRecordRawCutMetadata.terminal_count hn ht ha hR ctx
  have hi : i.val < (family (B).parameters (B).plan (B).data).birth
      ((B).key (IntegralMixedPhysicalMarkedTest.sampleContext ctx)) := by
    rw [hb]
    have h := i.isLt
    unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
    omega
  have hv := native_recipe (B)
    (IntegralMixedPhysicalMarkedPlan.leafSource hn ht ha (R := R) false)
    (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw i.val hi
  have hs := CoefficientMarkedRecordLeafNative.specializes hn ht ha hR ctx i.val i.isLt hlarge
  have hdim : CoefficientMarkedRecordLeafSign.count hn ht ha ctx =
      (CoefficientMarkedRecordLeafRecipe.arguments (B) (IntegralMixedPhysicalMarkedTest.sampleContext ctx)).dimension :=
    (CoefficientMarkedRecordCriticalFullSemantics.full_count hn ht ha hR ctx).trans
      (arguments_dimension (B) (IntegralMixedPhysicalMarkedTest.sampleContext ctx)).symm
  have he := @evaluate_heq (CoefficientMarkedRecordLeafSign.count hn ht ha ctx)
    (CoefficientMarkedRecordLeafRecipe.arguments (B) (IntegralMixedPhysicalMarkedTest.sampleContext ctx)).dimension hdim
    (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx)) (CoefficientMarkedRecordLeafSign.polynomial hn ht ha ctx i))
    (CoefficientMarkedRecordLeafNative.polynomial hn ht ha hR ctx i.val) hs z
    (tuple (B) (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw)
    (tuple_heq (B) (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw z hz).symm
  have hm := evaluate_map (R ctx) (CoefficientMarkedRecordLeafSign.polynomial hn ht ha ctx i) z
  exact hv.trans (congrArg (fun v : ℝ => InfinitesimalSign.encode (SignType.sign v)) (he.symm.trans hm))

end LeanCanny.Encoding.CoefficientMarkedRecordLeafValue
