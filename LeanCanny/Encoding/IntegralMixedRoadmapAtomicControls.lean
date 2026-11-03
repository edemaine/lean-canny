/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicLayout
public import LeanCanny.Encoding.IntegralMixedRoadmapVertexBudget
public import LeanCanny.Encoding.IntegralMixedPhysicalOriginalSource
/-! # Atomic vertex controls come from the actual original native bank -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapAtomic
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "A"=>IntegralMixedPhysicalMarkedPlan.native hn ht ha (radius_binary hR0) false

noncomputable def dimension (q :List Bool):=(B).parameters.ambient (root q)
noncomputable def initial (q :List Bool):=dimension hn ht ha hR0 q+5
noncomputable def width (q :List Bool):=(B).parameters.width (root q)
noncomputable def sourceCap (q :List Bool):=IntegralMixedExceptionalBounds.auxiliaryCap
  (dimension hn ht ha hR0 q+1) ((B).parameters.degree (root q))
noncomputable def scalarBudget (q :List Bool):=IntegralMixedRoadmapWidth.scalarBudget hn ht ha (original q)
noncomputable def wordBudget (q :List Bool):=IntegralMixedRoadmapWidth.vertexBudget hn ht ha (radius_binary hR0) (original q)

theorem dimension_unary :UnaryFn (dimension hn ht ha hR0):=(A).parameters.ambient.comp root_FP
theorem initial_unary :UnaryFn (initial hn ht ha hR0):=(dimension_unary hn ht ha hR0).add (UnaryFn.const 5)
theorem width_unary :UnaryFn (width hn ht ha hR0):=(A).parameters.width.comp root_FP
theorem sourceCap_binary :BinaryFn (sourceCap hn ht ha hR0):=
  IntegralMixedExceptionalBounds.auxiliaryCap_binary ((dimension_unary hn ht ha hR0).add (UnaryFn.const 1))
    ((A).parameters.degree.comp root_FP)
theorem scalarBudget_unary :UnaryFn (scalarBudget hn ht ha):=
  (IntegralMixedRoadmapWidth.scalarBudget_unary hn ht ha).comp original_FP
theorem wordBudget_unary :UnaryFn (wordBudget hn ht ha hR0):=
  (IntegralMixedRoadmapWidth.vertexBudget_unary hn ht ha (radius_binary hR0)).comp original_FP

theorem wordBudget_polynomial :∃p :Polynomial ℕ,∀q,wordBudget hn ht ha hR0 q≤p.eval (original q).length :=by
  obtain ⟨p,hp⟩:=IntegralMixedRoadmapWidth.vertexBudget_polynomial hn ht ha (radius_binary hR0)
  exact ⟨p,fun q=>hp (original q)⟩

theorem sourceCap_le (q :List Bool):sourceCap hn ht ha hR0 q≤2^width hn ht ha hR0 q :=
  (B).plan.scalar_cap (root q)

theorem dimension_eq (q :List Bool):dimension hn ht ha hR0 q=n (original q)+3 :=by
  change IntegralMixedAuxiliaryMarkedIntegerSource.number n (root q)+3=_
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,root,pairFst_pair,original]
theorem initial_eq (q :List Bool):initial hn ht ha hR0 q=n (original q)+8 :=by
  unfold initial
  rw [dimension_eq hn ht ha hR0 q]

def Canonical (q :List Bool):=q=packet (candidate q) (payload q) (word q) ∧
  candidate q=pair (original q) (pairSnd (candidate q))
theorem canonical_FP :FPPred Canonical:=
  (Brackets.stringEq_fppred id_mem_FP (mem_FP_pair candidate_FP (mem_FP_pair payload_FP word_FP))).and
    (Brackets.stringEq_fppred candidate_FP (mem_FP_pair original_FP (mem_FP_comp candidate_FP pairSnd_mem_FP)))

noncomputable def Grammar (q :List Bool):=Canonical q ∧
  IntegralMixedRoadmapChain.Checked (dimension hn ht ha hR0 q) (width hn ht ha hR0 q)
    (sourceCap hn ht ha hR0 q) (initial hn ht ha hR0 q) (scalarBudget hn ht ha q) (payload q) ∧
  (word q).length≤wordBudget hn ht ha hR0 q

theorem grammar_FP :FPPred (Grammar hn ht ha hR0):=canonical_FP.and
  ((IntegralMixedRoadmapChain.checkedAt_FP (dimension_unary hn ht ha hR0) (width_unary hn ht ha hR0)
    (sourceCap_binary hn ht ha hR0) (BinaryFn.ofUnary (initial_unary hn ht ha hR0))
    (scalarBudget_unary hn ht ha) payload_FP).and
    (FPPred.le (UnaryFn.length word_FP) (wordBudget_unary hn ht ha hR0)))

theorem native_companionQuery :
    (fun q=>companionQuery (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q)∈FP:=
  companionQuery_FP (dimension_unary hn ht ha hR0) (initial_unary hn ht ha hR0)
theorem native_signature :
    (fun q=>signature (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q)∈FP:=
  signature_FP (dimension_unary hn ht ha hR0) (initial_unary hn ht ha hR0)
end LeanCanny.Encoding.IntegralMixedRoadmapAtomic
