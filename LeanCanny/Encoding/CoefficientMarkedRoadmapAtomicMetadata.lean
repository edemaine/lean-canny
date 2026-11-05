/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRoadmapAtomicWordBudget
/-! # Atomic checked metadata survives radius and own-word replacement -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRoadmapAtomicMetadata
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapAtomic
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def reword (q w : List Bool) := packet (candidate q) (payload q) w

theorem candidate_reword (q w : List Bool) : candidate (reword q w) = candidate q := pairFst_pair _ _
theorem payload_reword (q w : List Bool) : payload (reword q w) = payload q := by
  simp only [reword, packet, payload, pairSnd_pair, pairFst_pair]
theorem word_reword (q w : List Bool) : word (reword q w) = w := by
  simp only [reword, packet, word, pairSnd_pair]
theorem original_reword (q w : List Bool) : original (reword q w) = original q :=
  congrArg pairFst (candidate_reword q w)
theorem root_reword (q w : List Bool) : root (reword q w) = root q := by
  simp only [root, candidate_reword, payload_reword]
theorem context_reword (q w : List Bool) : context (reword q w) = context q := congrArg (fun c => pair c []) (root_reword q w)

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)

theorem dimension_eq (q w : List Bool) : dimension hn ht ha hS (reword q w) = dimension hn ht ha hR q := by
  rw [IntegralMixedRoadmapAtomic.dimension_eq, IntegralMixedRoadmapAtomic.dimension_eq, original_reword]
theorem initial_eq (q w : List Bool) : initial hn ht ha hS (reword q w) = initial hn ht ha hR q := by
  rw [IntegralMixedRoadmapAtomic.initial_eq, IntegralMixedRoadmapAtomic.initial_eq, original_reword]
theorem width_eq (q w : List Bool) : width hn ht ha hS (reword q w) = width hn ht ha hR q := by
  change (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hS)).width (root (reword q w)) =
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR)).width (root q)
  rw [IntegralMixedRoadmapWidth.certified_width, IntegralMixedRoadmapWidth.certified_width, root_reword]
theorem sourceCap_eq (q w : List Bool) : sourceCap hn ht ha hS (reword q w) = sourceCap hn ht ha hR q := by
  unfold sourceCap
  rw [dimension_eq hn ht ha hR hS]
  congr 1
  change (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hS)).degree (root (reword q w)) =
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR)).degree (root q)
  rw [root_reword]
  rfl

/-- Target grammar follows from source grammar, the unchanged bounded
candidate label, and the fresh word's OWN validity. -/
theorem grammar_reword (q w : List Bool) (hg : Grammar hn ht ha hR q)
    (hlabel : (pairSnd (candidate q)).length ≤ IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha (original q))
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hS) false)
      (context q) w) : Grammar hn ht ha hS (reword q w) := by
  have hc := hg.2.1
  have hc' : IntegralMixedRoadmapChain.Checked (n (original q) + 3) (width hn ht ha hR q)
      (sourceCap hn ht ha hR q) (n (original q) + 8)
      (IntegralMixedRoadmapWidth.scalarBudget hn ht ha (original q)) (payload q) := by
    simpa only [IntegralMixedRoadmapAtomic.dimension_eq, IntegralMixedRoadmapAtomic.initial_eq, scalarBudget] using hc
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simp only [reword, packet, candidate, payload, word, pairFst_pair, pairSnd_pair]
    · simpa only [candidate_reword, original_reword] using hg.1.2
  · simpa only [dimension_eq hn ht ha hR hS, width_eq hn ht ha hR hS,
      sourceCap_eq hn ht ha hR hS, initial_eq hn ht ha hR hS, scalarBudget,
      original_reword, payload_reword] using hc
  · have hb := CoefficientMarkedRoadmapAtomicWordBudget.word_bound hn ht ha (candidate q) (payload q) w
      hc' hg.1.2 hlabel (radius_binary hS) hw
    simp only [wordBudget, word_reword]
    rw [original_reword]
    exact hb

end LeanCanny.Encoding.CoefficientMarkedRoadmapAtomicMetadata
