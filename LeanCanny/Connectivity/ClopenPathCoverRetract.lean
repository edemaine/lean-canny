/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ClopenPathCover
/-! # Transfer actual component labels through a section with connected fibers -/
@[expose] public section
namespace LeanCanny.Connectivity.ClopenPathCover
open Set
variable {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem mem_of_joined (C : ClopenPathCover Y I) (i : I) {y z : Y}
    (hy : y∈C.piece i) (h : JoinedIn univ y z) : z∈C.piece i := by
  obtain ⟨γ,_⟩ := h
  exact ((isPreconnected_range γ.continuous).subset_isClopen (C.clopen i)
    ⟨y,γ.source_mem_range,hy⟩) γ.target_mem_range

def retract (C : ClopenPathCover Y I) (p : Y → X) (s : X → Y)
    (hp : Continuous p) (hs : Continuous s) (hps : Function.LeftInverse p s)
    (hf : ∀ y, JoinedIn univ y (s (p y))) : ClopenPathCover X I where
  piece i := s ⁻¹' C.piece i
  clopen i := (C.clopen i).preimage hs
  cover x := C.cover (s x)
  paths := by
    intro i x hx y hy
    have H := (C.paths i (s x) hx (s y) hy).map hp.continuousOn
    rw [hps x,hps y] at H
    apply H.mono
    rintro z ⟨w,hw,rfl⟩
    exact C.mem_of_joined i hw (hf w)

theorem retract_piece (C : ClopenPathCover Y I) (p : Y → X) (s : X → Y)
    (hp : Continuous p) (hs : Continuous s) (hps : Function.LeftInverse p s)
    (hf : ∀ y, JoinedIn univ y (s (p y))) (i : I) :
    (C.retract p s hp hs hps hf).piece i=p '' C.piece i := by
  ext x
  constructor
  · intro hx
    exact ⟨s x,hx,hps x⟩
  · rintro ⟨y,hy,rfl⟩
    exact C.mem_of_joined i hy (hf y)
end LeanCanny.Connectivity.ClopenPathCover
