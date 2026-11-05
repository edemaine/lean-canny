/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedCriticalPrefixIncidence
/-! # Allocate the parent word BEFORE embedding it in its own query -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalParentWord
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem candidate_context (I : SquareSampleInput.Inputs) (q r w : List Bool) (he : q = r)
    (hq : SquareSampleCompleteVertices.Valid I q w) (hr : SquareSampleCompleteVertices.Valid I r w) :
    HEq (SquareSampleCompleteVertices.candidate I q w hq).val (SquareSampleCompleteVertices.candidate I r w hr).val := by
  subst r
  rfl

private theorem candidate_factor (I J : SquareSampleInput.Inputs) (f : List Bool → List Bool)
    (he : I = SquareSampleInput.comp J f) (q r w : List Bool) (hf : f q = f r)
    (hq : SquareSampleCompleteVertices.Valid I q w) (hr : SquareSampleCompleteVertices.Valid I r w) :
    HEq (SquareSampleCompleteVertices.candidate I q w hq).val (SquareSampleCompleteVertices.candidate I r w hr).val := by
  cases he
  have hJq := (SquareSampleCompleteNaturality.complete_valid_comp J f q w).mp hq
  have hJr := (SquareSampleCompleteNaturality.complete_valid_comp J f r w).mp hr
  have ha := SquareSampleCompleteNaturality.candidate_comp J f q w hq hJq
  have hb := SquareSampleCompleteNaturality.candidate_comp J f r w hr hJr
  exact (heq_of_eq ha).trans ((candidate_context J (f q) (f r) w hf hJq hJr).trans (heq_of_eq hb.symm))

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)

/-- Every genuine prepared-parent row tuple obtains a fresh OWN word even
when the resulting query embeds that very word. Context naturality preserves
the ENTIRE raw tuple; allocation does not solve a word-in-own-context equation. -/
theorem exists_self_word (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q))
    (z : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage false q) (Nat.sub_le _ _)).count → ℝ)
    (hz : CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage false q) (Nat.sub_le _ _) ((2 : ℝ)^R (IntegralMixedPhysicalCriticalQuery.root q)) z) :
    ∃ w, ∃ hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false false)
      (pair (IntegralMixedPhysicalCriticalQuery.root q) (pair w [])) w,
      w.length = SquareSampleCompleteVertices.width (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false false)
        (pair (IntegralMixedPhysicalCriticalQuery.root q) (pair w [])) ∧
      HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false false)
        (pair (IntegralMixedPhysicalCriticalQuery.root q) (pair w [])) w hw).val z := by
  obtain ⟨w, hw, hl, he⟩ := CoefficientMarkedCriticalPrefixIncidence.exists_word hn ht ha hR false q hc hlarge z hz
  let r := pair (IntegralMixedPhysicalCriticalQuery.root q) (pair w [])
  have hroot : pairFst q = pairFst r := (pairFst_pair (IntegralMixedPhysicalCriticalQuery.root q) (pair w [])).symm
  have hr := (IntegralMixedPhysicalCriticalParentContext.valid_iff hn ht ha hR q r w hroot).mp hw
  have htuple := candidate_factor (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false false)
    (IntegralMixedPhysicalCriticalParentContext.rootInput hn ht ha hR) pairFst
    (IntegralMixedPhysicalCriticalParentContext.input_factor hn ht ha hR) q r w hroot hw hr
  exact ⟨w, hr, hl.trans (IntegralMixedPhysicalCriticalParentContext.width_eq hn ht ha hR q r hroot), htuple.symm.trans he⟩

end LeanCanny.Encoding.CoefficientMarkedCriticalParentWord
