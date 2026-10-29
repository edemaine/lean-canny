/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineFullSourceTower

/-! # Native context changes preserve every affine tower record -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineFullSourceContext
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open FlatAffineFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def query (f : List Bool → List Bool) (q : List Bool) : List Bool := pair (f (pairFst q)) (pairSnd q)
def levelQuery (f : List Bool → List Bool) (q : List Bool) : List Bool := pair (query f (pairFst q)) (pairSnd q)

theorem query_FP {f : List Bool → List Bool} (hf : f ∈ FP) : query f ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP

theorem levelQuery_FP {f : List Bool → List Bool} (hf : f ∈ FP) : levelQuery f ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP (query_FP hf)) pairSnd_mem_FP

theorem query_stage (f : List Bool → List Bool) (u : List Bool) (k : ℕ) :
    query f (FlatAffineFullSourceTower.stage u k) = FlatAffineFullSourceTower.stage (f u) k := by
  simp only [query, FlatAffineFullSourceTower.stage, pairFst_pair, pairSnd_pair]

theorem query_level (f : List Bool → List Bool) (u : List Bool) (k j : ℕ) :
    levelQuery f (FlatAffineFullSourceTower.levelQuery u k j) = FlatAffineFullSourceTower.levelQuery (f u) k j := by
  simp only [levelQuery, FlatAffineFullSourceTower.levelQuery, pairFst_pair, pairSnd_pair, query_stage]

noncomputable def comp (F : Inputs) (f : List Bool → List Bool) : Inputs where
  source := F.source.comp f
  depth := F.depth ∘ f
  width := F.width ∘ f
  direction := F.direction ∘ query f
  level := F.level ∘ levelQuery f

theorem access {F : Inputs} (h : F.Access) {f : List Bool → List Bool} (hf : f ∈ FP) : (comp F f).Access :=
  ⟨h.source.comp hf, h.depth.comp hf, h.width.comp hf, h.direction.precompose _ (query_FP hf),
    h.level.precompose _ (levelQuery_FP hf), fun u => h.sourceArity (f u)⟩

theorem polynomial_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) :
    BoundedFullCriticalSamples.polynomial (comp F f).source u = BoundedFullCriticalSamples.polynomial F.source (f u) := by
  change BoundedFullCriticalSamples.polynomial (F.source.comp f) u = _
  unfold BoundedFullCriticalSamples.polynomial
  rw [BoundedFullWriter.original_comp, BoundedFullWriter.size_comp]
  rfl

theorem free_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) (k : ℕ) :
    FlatAffineFullSourceTower.free (comp F f) u k = FlatAffineFullSourceTower.free F (f u) k := by
  ext j
  simp only [FlatAffineFullSourceTower.free, comp, Function.comp_apply, query_level]
  rfl

theorem direction_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) (k : ℕ)
    (r : Fin (FlatAffineFullSourceTower.arity F (f u) + 1)) (i : Fin (FlatAffineFullSourceTower.arity F (f u))) :
    FlatAffineFullSourceTower.direction (comp F f) u k r i = FlatAffineFullSourceTower.direction F (f u) k r i := by
  simp only [FlatAffineFullSourceTower.direction, comp, Function.comp_apply, query_stage]
  rfl

theorem level_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) (k : ℕ)
    (j : Fin (FlatAffineFullSourceTower.arity F (f u))) :
    FlatAffineFullSourceTower.level (comp F f) u k j = FlatAffineFullSourceTower.level F (f u) k j := by
  simp only [FlatAffineFullSourceTower.level, comp, Function.comp_apply, query_level]
  rfl

theorem family_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) :
    FlatAffineFullSourceTower.family (comp F f) u = FlatAffineFullSourceTower.family F (f u) := by
  have hs := funext (free_comp F f u)
  have ha := funext (fun k => funext (fun r => funext (direction_comp F f u k r)))
  have hb := funext (fun k => funext (level_comp F f u k))
  unfold FlatAffineFullSourceTower.family
  rw [polynomial_comp, hs, ha, hb]

theorem system_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool)
    (i : Fin (FlatAffineFullSourceTower.count F (f u))) :
    FlatAffineFullSourceTower.system (comp F f) u i = FlatAffineFullSourceTower.system F (f u) i := by
  unfold FlatAffineFullSourceTower.system
  rw [family_comp]
  rfl

end LeanCanny.Encoding.FlatAffineFullSourceContext
