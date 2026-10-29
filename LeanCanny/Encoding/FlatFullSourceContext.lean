/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceTower

/-! # Native context changes for the complete flat source

Changing the source context preserves every stage field. Stage numbers stay
attached to the transformed source input. All source, direction, and metadata
costs are included, and the resulting family is exactly the old family at
that source input.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceContext
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open FlatFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def query (f : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (f (pairFst q)) (pairSnd q)

theorem query_FP {f : List Bool → List Bool} (hf : f ∈ FP) : query f ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP

theorem query_stage (f : List Bool → List Bool) (u : List Bool) (k : ℕ) :
    query f (FlatFullSourceTower.stage u k) = FlatFullSourceTower.stage (f u) k := by
  simp only [query, FlatFullSourceTower.stage, pairFst_pair, pairSnd_pair]

noncomputable def comp (F : Inputs) (f : List Bool → List Bool) : Inputs where
  source := F.source.comp f
  depth := F.depth ∘ f
  width := F.width ∘ f
  offset := F.offset ∘ query f
  dim := F.dim ∘ query f
  direction := F.direction ∘ query f
  pivot u k := F.pivot (f u) k

theorem access {F : Inputs} (h : F.Access) {f : List Bool → List Bool} (hf : f ∈ FP) : (comp F f).Access := by
  refine ⟨h.source.comp hf, h.depth.comp hf, h.width.comp hf,
    h.offset.comp (query_FP hf), h.dim.comp (query_FP hf),
    h.direction.precompose _ (query_FP hf), ?_, fun u => h.sourceArity (f u)⟩
  apply BinaryFn.of_eq (h.pivot.comp (query_FP hf))
  intro q
  change (F.pivot (pairFst (query f q)) (Nat.fromBitsLE (pairSnd (query f q)))).val = _
  have h0 : pairFst (query f q) = f (pairFst q) := pairFst_pair _ _
  have h1 : pairSnd (query f q) = pairSnd q := pairSnd_pair _ _
  rw [h0, h1]
  rfl

theorem degree_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) :
    FlatFullSourceTower.degree (comp F f) u = FlatFullSourceTower.degree F (f u) := rfl

theorem polynomial_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) :
    BoundedFullCriticalSamples.polynomial (comp F f).source u = BoundedFullCriticalSamples.polynomial F.source (f u) := by
  change BoundedFullCriticalSamples.polynomial (F.source.comp f) u = _
  unfold BoundedFullCriticalSamples.polynomial
  rw [BoundedFullWriter.original_comp, BoundedFullWriter.size_comp]
  rfl

theorem free_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) (k : ℕ) :
    FlatFullSourceTower.free (comp F f) u k = FlatFullSourceTower.free F (f u) k := by
  ext i
  simp only [FlatFullSourceTower.free, Finset.mem_filter, Finset.mem_univ, true_and]
  change (F.offset (query f (FlatFullSourceTower.stage u k)) ≤ i.val ∧
    i.val < F.offset (query f (FlatFullSourceTower.stage u k)) + F.dim (query f (FlatFullSourceTower.stage u k))) ↔ _
  rw [query_stage]

theorem direction_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) (k : ℕ)
    (i : Fin (FlatFullSourceTower.arity F (f u))) :
    FlatFullSourceTower.direction (comp F f) u k i = FlatFullSourceTower.direction F (f u) k i := by
  simp only [FlatFullSourceTower.direction, comp, Function.comp_apply, query_stage]

theorem family_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) :
    FlatFullSourceTower.family (comp F f) u = FlatFullSourceTower.family F (f u) := by
  have hs := funext (free_comp F f u)
  have hv := funext (fun k => funext (direction_comp F f u k))
  change FlatCriticalTower.family (BoundedFullCriticalSamples.polynomial (comp F f).source u)
    (FlatFullSourceTower.free (comp F f) u) (F.pivot (f u)) (FlatFullSourceTower.direction (comp F f) u) = _
  rw [polynomial_comp, hs, hv]
  rfl

theorem system_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool)
    (i : Fin (FlatFullSourceTower.count F (f u))) :
    FlatFullSourceTower.system (comp F f) u i = FlatFullSourceTower.system F (f u) i := by
  unfold FlatFullSourceTower.system
  rw [family_comp]
  rfl

end LeanCanny.Encoding.FlatFullSourceContext
