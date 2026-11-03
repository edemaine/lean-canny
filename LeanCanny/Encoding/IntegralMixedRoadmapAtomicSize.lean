/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapChainMetadataSize
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicVertex
/-! # Every accepted atomic vertex has an original polynomial byte bound

The bound includes candidate, full history metadata, raw records, terminal
record and full sampler word. It applies to all accepted vertices.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapAtomic
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)

noncomputable def byteBudget (u : List Bool):=2*IntegralMixedRoadmapWidth.candidateBudget hn ht ha u+
  2*IntegralMixedRoadmapChain.payloadBudget (n u+3) (n u+8) (IntegralMixedRoadmapWidth.scalarBudget hn ht ha u)+
  IntegralMixedRoadmapWidth.vertexBudget hn ht ha (radius_binary hR0) u+4

theorem byteBudget_unary : UnaryFn (byteBudget hn ht ha hR0):=by
  have HC:=IntegralMixedRoadmapWidth.candidateBudget_unary hn ht ha
  have HP:=IntegralMixedRoadmapChain.payloadBudget_unary (hn.add (UnaryFn.const 3))
    (hn.add (UnaryFn.const 8)) (IntegralMixedRoadmapWidth.scalarBudget_unary hn ht ha)
  have HW:=IntegralMixedRoadmapWidth.vertexBudget_unary hn ht ha (radius_binary hR0)
  exact ((((UnaryFn.const 2).mul HC).add ((UnaryFn.const 2).mul HP)).add HW).add (UnaryFn.const 4)

theorem byteBudget_polynomial : ∃p : Polynomial ℕ,∀u,byteBudget hn ht ha hR0 u≤p.eval u.length :=by
  obtain ⟨p,hp⟩:=output_length_poly_of_mem_FP (byteBudget_unary hn ht ha hR0).mem_FP
  exact ⟨p,fun u=>by simpa only [List.length_replicate] using hp u⟩

theorem payload_byte_bound (q : List Bool) (hv : Valid hn ht ha hR0 q) :
    (payload q).length≤IntegralMixedRoadmapChain.payloadBudget (n (original q)+3) (n (original q)+8)
      (IntegralMixedRoadmapWidth.scalarBudget hn ht ha (original q)) :=by
  have HP:=IntegralMixedRoadmapChain.payload_length (checked hn ht ha hR0 q hv)
  simpa only [dimension_eq hn ht ha hR0,initial_eq hn ht ha hR0,scalarBudget] using HP

theorem byte_bound (q : List Bool) (hv : Valid hn ht ha hR0 q) : q.length≤byteBudget hn ht ha hR0 (original q) :=by
  have HC:=candidate_byte_bound hn ht ha hR0 q hv
  have HP:=payload_byte_bound hn ht ha hR0 q hv
  have HW:=word_bound hn ht ha hR0 q hv
  have HE:=congrArg List.length hv.1.1.1
  simp only [packet,pair_length] at HE
  unfold byteBudget wordBudget at *
  omega

theorem polynomial_byte_bound : ∃p : Polynomial ℕ,∀q,Valid hn ht ha hR0 q→q.length≤p.eval (original q).length :=by
  obtain ⟨p,hp⟩:=byteBudget_polynomial hn ht ha hR0
  exact ⟨p,fun q hq=>(byte_bound hn ht ha hR0 q hq).trans (hp (original q))⟩

end LeanCanny.Encoding.IntegralMixedRoadmapAtomic
