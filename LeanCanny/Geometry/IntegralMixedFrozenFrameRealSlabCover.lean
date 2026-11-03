/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSlabCover
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealInterior
/-! # Actual real-critical-value variant of the frame slab construction -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem exists_slab_cover_of_realCriticalValues {L R : Type} [Finite L] [Finite R] (x : State P S B m ι) (hm : m≤S)
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
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (left : ClopenPathCover ((coarseProjection P F values h) ⁻¹' {A}) L)
    (right : ClopenPathCover ((coarseProjection P F values h) ⁻¹' {B}) R) :
    let I:=IntegralMixedSelectedPhysicalFiber.physical
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm (sweep x F h hh g hg) φ t₀.val
    Finite I ∧ Nonempty (ClopenPathCover ((coarseProjection P F values h) ⁻¹' Icc A B)
      (ComponentSlabCover.SelectedIndex I L R)) := by
  obtain ⟨Hfin,D,_,_,_⟩:=exists_interior_data_of_realCriticalValues x hm φ F h hh g hg values H c A B t₀ havoid hheight hp
  let : Finite (IntegralMixedSelectedPhysicalFiber.physical
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm (sweep x F h hh g hg) φ t₀.val):=Hfin
  obtain ⟨l,r,HS⟩:=ComponentSlabCover.exists_selection D left right
  have HP:=coarseProjection_continuous P F values h
  have HAB:=t₀.property.1.trans t₀.property.2
  exact ⟨Hfin,⟨ClopenPathCover.ofClosed (ComponentSlabCover.selectedPiece D left right l r)
    (ComponentSlabCover.selected_closed D left right l r HP)
    (ComponentSlabCover.selected_cover D left right l r HS)
    (ComponentSlabCover.selected_paths D left right l r HP HAB t₀)⟩⟩

end LeanCanny.Geometry.IntegralMixedFrozenFrame
