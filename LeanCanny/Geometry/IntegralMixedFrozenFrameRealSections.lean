/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSections
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealRegular
/-! # Actual real-critical-value variant of the frame slab construction -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem exists_sections_of_realCriticalValues (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (g : Fin (n+1)) (hg : g∉F.frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (c : IntegralMixedRelativeCuts.Choices
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm (sweep x F h hh g hg) φ)
    (A B : ℝ) (t₀ : Ioo A B)
    (havoid : ∀ t∈Ioo A B,t∉IntegralMixedSelectedCriticalCuts.bad
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm (sweep x F h hh g hg) φ c)
    (hheight : ∀ t∈Ioo A B,t∉realCriticalValues P F values h)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y)) :
    let e:=FrozenCoordinateOrdering.permutation F.frozen
    let I:=IntegralMixedSelectedPhysicalFiber.physical (IntegralMixedCoordinateRename.state x e) hm (sweep x F h hh g hg) φ t₀.val
    Finite I ∧ ∃ curve : I→ℝ→Fin (n+1)→ℝ,
      (∀ j,curve j t₀.val=j.val ∘ e.symm) ∧
      (∀ j,ContinuousOn (curve j) (Icc A B)) ∧
      (∀ j t,t∈Icc A B→curve j t∈shiftedSlice P F values h t) ∧
      ∀ t : Ioo A B,∀ y∈shiftedSlice P F values h t.val,∃ j,
        JoinedIn (shiftedSlice P F values h t.val) y (curve j t.val) := by
  let e:=FrozenCoordinateOrdering.permutation F.frozen
  let x':=IntegralMixedCoordinateRename.state x e
  let r:=sweep x F h hh g hg
  obtain ⟨Hfin,curve,HA,HC,HR,HE,_⟩:=IntegralMixedSelectedPhysicalArcs.anchored_physical_arcs
    x' hm r φ c A B t₀ havoid
  refine ⟨Hfin,fun j t=>curve j t ∘ e.symm,?_,?_,?_,?_⟩
  · intro j
    exact congrArg (fun z=>z ∘ e.symm) (HA j)
  · intro j
    exact (continuous_pi (fun i=>continuous_apply (e.symm i))).comp_continuousOn (HC j)
  · intro j t ht
    exact physical_mem_shiftedSlice x hm φ F h hh g hg values H t (curve j t) (HR j t ht)
  · intro t y hy
    obtain ⟨a,ha,hphys⟩:=exists_path_sample_of_realCriticalValues x hm φ F h hh g hg values H t.val (hheight t.val t.property) y hy hp
    obtain ⟨j,Hj,_⟩:=(HE t (a ∘ e)).mp hphys
    refine ⟨j,?_⟩
    change JoinedIn (shiftedSlice P F values h t.val) y (curve j t.val ∘ e.symm)
    rw [Hj]
    simpa only [Function.comp_def,Equiv.apply_symm_apply] using ha

end LeanCanny.Geometry.IntegralMixedFrozenFrame
