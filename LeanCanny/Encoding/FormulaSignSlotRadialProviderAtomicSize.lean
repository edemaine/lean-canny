/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicValid
public import LeanCanny.Encoding.IntegralMixedRoadmapChainMetadataSize
/-! # Accepted provider vertices have a fixed-provider polynomial byte bound -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def providerPayloadBudget (c : List Bool) := IntegralMixedRoadmapChain.payloadBudget
  (FormulaSignSlotRadialProviderIntegerPlan.parameters.ambient c)
  (FormulaSignSlotRadialProviderIntegerPlan.count c)
  (FormulaSignSlotRadialProviderIntegerPlan.parameters.width c)
theorem providerPayloadBudget_unary : UnaryFn providerPayloadBudget :=
  IntegralMixedRoadmapChain.payloadBudget_unary FormulaSignSlotRadialProviderIntegerPlan.access.ambient
    FormulaSignSlotRadialProviderIntegerPlan.count_unary FormulaSignSlotRadialProviderIntegerPlan.access.width

theorem payload_length_provider (q : List Bool) (h : Valid q) :
    (payload q).length≤providerPayloadBudget (provider q) := by
  have HI : initial q=FormulaSignSlotRadialProviderIntegerPlan.count (provider q) := initial_provider q
  simpa only [providerPayloadBudget,dimension_provider,width_provider,HI] using payload_length q h.1

noncomputable def providerVertexBudget (c : List Bool) :=
  2*c.length+2*providerPayloadBudget c+providerWordBudget c+4
theorem providerVertexBudget_unary : UnaryFn providerVertexBudget :=
  ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add
    ((UnaryFn.const 2).mul providerPayloadBudget_unary)).add providerWordBudget_unary).add (UnaryFn.const 4)

theorem vertex_length_provider (q : List Bool) (h : Valid q) : q.length≤providerVertexBudget (provider q) := by
  have HP := payload_length_provider q h
  have HW := valid_word_bound q h
  have HE := congrArg List.length (valid_grammar q h).1
  simp only [packet,pair_length] at HE
  unfold providerVertexBudget
  omega

theorem provider_vertex_polynomial : ∃p : Polynomial ℕ,∀q,Valid q→q.length≤p.eval (provider q).length := by
  obtain ⟨p,hp⟩ := output_length_poly_of_mem_FP providerVertexBudget_unary.mem_FP
  refine ⟨p,fun q h=>(vertex_length_provider q h).trans ?_⟩
  simpa only [List.length_replicate] using hp (provider q)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
