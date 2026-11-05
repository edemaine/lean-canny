/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalParentContext
/-! # Entire own-tuple transport between the actual critical contexts -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalWordContext
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem candidate_same (I : SquareSampleInput.Inputs) (q r w : List Bool) (he : q = r)
    (hq : SquareSampleCompleteVertices.Valid I q w) (hr : SquareSampleCompleteVertices.Valid I r w) :
    HEq (SquareSampleCompleteVertices.candidate I q w hq).val (SquareSampleCompleteVertices.candidate I r w hr).val := by
  subst r
  rfl

private theorem candidate_factor (I J K : SquareSampleInput.Inputs) (f g : List Bool → List Bool)
    (hi : I = SquareSampleInput.comp K f) (hj : J = SquareSampleInput.comp K g)
    (q r w : List Bool) (he : f q = g r)
    (hq : SquareSampleCompleteVertices.Valid I q w) (hr : SquareSampleCompleteVertices.Valid J r w) :
    HEq (SquareSampleCompleteVertices.candidate I q w hq).val (SquareSampleCompleteVertices.candidate J r w hr).val := by
  cases hi
  cases hj
  have hkq := (SquareSampleCompleteNaturality.complete_valid_comp K f q w).mp hq
  have hkr := (SquareSampleCompleteNaturality.complete_valid_comp K g r w).mp hr
  have ha := SquareSampleCompleteNaturality.candidate_comp K f q w hq hkq
  have hb := SquareSampleCompleteNaturality.candidate_comp K g r w hr hkr
  exact (heq_of_eq ha).trans ((candidate_same K _ _ w he hkq hkr).trans (heq_of_eq hb.symm))

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  SquareSampleCompleteVertices.Valid

/-- AUX changes preserve the ENTIRE tuple because the complete sampler inputs
factor through ROOT, including their numerical sampling metadata. -/
theorem candidate_context (child : Bool) (q r w : List Bool) (he : pairFst q = pairFst r)
    (hq : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) q w)
    (hr : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) r w) :
    HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) q w hq).val
      (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) r w hr).val := by
  cases child
  · exact candidate_factor _ _ (IntegralMixedPhysicalCriticalParentContext.rootInput hn ht ha hR) pairFst pairFst
      (IntegralMixedPhysicalCriticalParentContext.input_factor hn ht ha hR)
      (IntegralMixedPhysicalCriticalParentContext.input_factor hn ht ha hR) q r w he hq hr
  · exact candidate_factor _ _ (IntegralMixedPhysicalMarkedContext.rootInput hn ht ha hR) pairFst pairFst
      (IntegralMixedPhysicalCriticalContext.input_factor hn ht ha hR)
      (IntegralMixedPhysicalCriticalContext.input_factor hn ht ha hR) q r w he hq hr

/-- The prepared full word has exactly the standard marked full tuple at that
ROOT. This reuses its own word at the same radius; it does not rebase a word. -/
theorem candidate_full (q w : List Bool)
    (hq : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true) q w)
    (hr : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalCriticalContext.context q) w) :
    HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true) q w hq).val
      (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
        (IntegralMixedPhysicalCriticalContext.context q) w hr).val := by
  exact candidate_factor _ _ (IntegralMixedPhysicalMarkedContext.rootInput hn ht ha hR) pairFst pairFst
    (IntegralMixedPhysicalCriticalContext.input_factor hn ht ha hR)
    (IntegralMixedPhysicalMarkedContext.input_factor hn ht ha hR) q _ w
    (by simp only [IntegralMixedPhysicalCriticalContext.context, IntegralMixedPhysicalCriticalQuery.root, pairFst_pair]) hq hr

theorem width_context (child : Bool) (q r : List Bool) (he : pairFst q = pairFst r) :
    SquareSampleCompleteVertices.width (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) q =
      SquareSampleCompleteVertices.width (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) r := by
  cases child
  · exact IntegralMixedPhysicalCriticalParentContext.width_eq hn ht ha hR q r he
  · rw [IntegralMixedPhysicalCriticalContext.input_factor,
      SquareSampleCompleteNaturality.complete_width_comp, SquareSampleCompleteNaturality.complete_width_comp, he]

end LeanCanny.Encoding.CoefficientMarkedCriticalWordContext
