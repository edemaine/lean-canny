/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedCriticalBankIncidence
public import LeanCanny.Encoding.CoefficientMarkedCriticalCorrelationIncidence
public import LeanCanny.Encoding.CoefficientMarkedCriticalIntervalIncidence
/-! # Exact coupled raw-tuple predicate for the native critical search -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalIntervalPredicate
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable abbrev Point (child : Bool) (q : List Bool) :=
  Fin (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
    (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _)).count → ℝ

noncomputable def Tests (q : List Bool) (β : ℝ) (parent : Point hn ht ha false q) (child : Point hn ht ha true q) : Prop :=
  CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha q β parent child ∧
    (CoefficientMarkedCriticalCorrelationIncidence.polynomial hn ht ha q).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation β) child = 0 ∧
    SignType.sign ((CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha false
      (IntegralMixedPhysicalCriticalQuery.root q)).eval₂ (SymbolicScaledSquarefree.scalarEvaluation β) child) = 1 ∧
    SignType.sign ((CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha true
      (IntegralMixedPhysicalCriticalQuery.root q)).eval₂ (SymbolicScaledSquarefree.scalarEvaluation β) child) = 1

/-- The parent stays FIXED while every complete child raw-root tuple is tested.
The same child tuple supplies bank incidence, correlation and both inequalities. -/
noncomputable def Counterexample (q : List Bool) (β : ℝ) (parent : Point hn ht ha false q) : Prop :=
  ∃ child : Point hn ht ha true q,
    CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage true q) (Nat.sub_le _ _) β child ∧
    Tests hn ht ha q β parent child

variable {R : List Bool → ℕ} (hR : BinaryFn R)

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family CoefficientMarkedRecordRows.symbolic
  CoefficientMarkedCriticalBankIncidence.Agrees CoefficientMarkedCriticalCorrelationIncidence.polynomial
  CoefficientMarkedCriticalIntervalQuery.polynomial SquareSampleCompleteVertices.Valid

private theorem witness_iff (q : List Bool) (hg : IntegralMixedPhysicalCriticalInterval.Guard n false q)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q))
    (hp : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false false)
      q (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (parent : Point hn ht ha false q)
    (heParent : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q) hp).val parent)
    (w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true) q w)
    (child : Point hn ht ha true q)
    (heChild : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true) q w hw).val child) :
    pair q w ∈ IntegralMixedPhysicalCriticalInterval.witnessLanguage hn ht ha hR false ↔
      Tests hn ht ha q ((2 : ℝ)^R (IntegralMixedPhysicalCriticalQuery.root q)) parent child := by
  have hb := CoefficientMarkedCriticalBankIncidence.agrees_iff hn ht ha hR q hg.1.1 hlarge
    (IntegralMixedPhysicalCriticalQuery.parentWord q) w rfl hp hw parent child heParent heChild
  have hc : IntegralMixedPhysicalCriticalInterval.correlation hn ht ha hR false (pair q w) = InfinitesimalSign.encode 0 ↔
      (CoefficientMarkedCriticalCorrelationIncidence.polynomial hn ht ha q).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R (IntegralMixedPhysicalCriticalQuery.root q))) child = 0 := by
    rw [CoefficientMarkedCriticalCorrelationIncidence.value_eq hn ht ha hR q hlarge w hw child heChild,
      SquareSampleTestSign.encode_eq_iff, sign_eq_zero_iff]
  have hi (upper : Bool) : IntegralMixedPhysicalCriticalInterval.value hn ht ha hR false upper (pair q w) = InfinitesimalSign.encode 1 ↔
      SignType.sign ((CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha upper
        (IntegralMixedPhysicalCriticalQuery.root q)).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R (IntegralMixedPhysicalCriticalQuery.root q))) child) = 1 := by
    rw [CoefficientMarkedCriticalIntervalIncidence.value_eq hn ht ha hR upper q hlarge w hw child heChild,
      SquareSampleTestSign.encode_eq_iff]
  have hnativ : pair q w ∈ IntegralMixedPhysicalCriticalInterval.witnessLanguage hn ht ha hR false ↔
      IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha hR false (pair q w) ∧
      IntegralMixedPhysicalCriticalInterval.correlation hn ht ha hR false (pair q w) = InfinitesimalSign.encode 0 ∧
      IntegralMixedPhysicalCriticalInterval.value hn ht ha hR false false (pair q w) = InfinitesimalSign.encode 1 ∧
      IntegralMixedPhysicalCriticalInterval.value hn ht ha hR false true (pair q w) = InfinitesimalSign.encode 1 := by
    simp only [IntegralMixedPhysicalCriticalInterval.witnessLanguage, Set.mem_ofPred_eq,
      pairFst_pair, pairSnd_pair, hg, hp, hw, true_and]
  exact hnativ.trans (and_congr hb (and_congr hc (and_congr (hi false) (hi true))))

private theorem witness_child (q w : List Bool)
    (hh : pair q w ∈ IntegralMixedPhysicalCriticalInterval.witnessLanguage hn ht ha hR false) :
    SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true) q w := by
  simpa only [pairFst_pair, pairSnd_pair] using hh.2.2.1

attribute [local irreducible] IntegralMixedPhysicalCriticalInterval.witnessLanguage

/-- Exact native search incidence. No independent family, quotient agreement,
guard acceptance, homomorphism, or interpreted critical-point premise is assumed. -/
theorem language_iff (q : List Bool) (hg : IntegralMixedPhysicalCriticalInterval.Guard n false q)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q))
    (hp : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false false)
      q (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (parent : Point hn ht ha false q)
    (heParent : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q) hp).val parent) :
    q ∈ IntegralMixedPhysicalCriticalInterval.language hn ht ha hR false ↔
      Counterexample hn ht ha q ((2 : ℝ)^R (IntegralMixedPhysicalCriticalQuery.root q)) parent := by
  constructor
  · rintro ⟨w, _, hh⟩
    have hw := witness_child hn ht ha hR q w hh
    obtain ⟨child, hrows, heChild⟩ := CoefficientMarkedCriticalPrefixIncidence.rows_of_word hn ht ha hR true q hg.1.1 hlarge w hw
    exact ⟨child, hrows, (witness_iff hn ht ha hR q hg hlarge hp parent heParent w hw child heChild).mp hh⟩
  · rintro ⟨child, hrows, htests⟩
    obtain ⟨w, hw, hlen, heChild⟩ := CoefficientMarkedCriticalPrefixIncidence.exists_word hn ht ha hR true q hg.1.1 hlarge child hrows
    exact ⟨w, hlen, (witness_iff hn ht ha hR q hg hlarge hp parent heParent w hw child heChild).mpr htests⟩

end LeanCanny.Encoding.CoefficientMarkedCriticalIntervalPredicate
