/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FiniteSlabEndpointPaths
/-! # Replacing every cut point by a representative in the same fiber -/
@[expose] public section
namespace LeanCanny.Connectivity.FiniteSlabEndpointPaths
open Set
variable {X :Type*} [TopologicalSpace X] {n :ℕ}
variable (p :X→ℝ) (cut :ℕ→ℝ) (representative :CutPoint p cut n→CutPoint p cut n)
  (height :∀z,p (representative z).val=p z.val)
  (fiber :∀z,JoinedIn (p ⁻¹' {p z.val}) z.val (representative z).val)

include height fiber in
/-- A same-fiber replacement at each end preserves the actual closed-slab
path and BOTH of its endpoint heights. No cover or regularity is assumed. -/
theorem slabStep_map_fiber {x y :CutPoint p cut n} (H :SlabStep p cut x y):
    SlabStep p cut (representative x) (representative y):=by
  obtain ⟨i,hx,hy,hpath⟩:=H
  have HL:JoinedIn (p ⁻¹' Icc (cut i.val) (cut (i.val+1))) (representative x).val x.val:=
    (fiber x).symm.mono (by
      intro z hz
      change p z=p x.val at hz
      change p z∈Icc (cut i.val) (cut (i.val+1))
      rw [hz]
      exact hpath.source_mem)
  have HR:JoinedIn (p ⁻¹' Icc (cut i.val) (cut (i.val+1))) y.val (representative y).val:=
    (fiber y).mono (by
      intro z hz
      change p z=p y.val at hz
      change p z∈Icc (cut i.val) (cut (i.val+1))
      rw [hz]
      exact hpath.target_mem)
  exact ⟨i,hx.imp ((height x).trans) ((height x).trans),
    hy.imp ((height y).trans) ((height y).trans),HL.trans (hpath.trans HR)⟩

include height fiber in
/-- Map EVERY intermediate point of the finite endpoint walk, rather than
assuming the original boundary points satisfy the representative equations. -/
theorem endpointReach_map_fiber {x y :CutPoint p cut n} (H :EndpointReach p cut x y):
    EndpointReach p cut (representative x) (representative y):=by
  induction H with
  | refl=>exact .refl
  | tail H hedge ih=>exact ih.tail (slabStep_map_fiber p cut representative height fiber hedge)

end LeanCanny.Connectivity.FiniteSlabEndpointPaths
