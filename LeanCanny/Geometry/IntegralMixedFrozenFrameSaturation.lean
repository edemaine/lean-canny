/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFramePaths
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSampling

/-! # Every regular full-fiber point reaches an actual selected critical sample -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem exists_path_sample (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (g : Fin (n+1)) (hg : g∉F.frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (ht : (heightCut x hm F h).eval₂ φ.toRingHom t≠0)
    (y : Fin (n+1)→ℝ) (hy : y∈shiftedSlice P F values h t)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y)) :
    ∃ a : Fin (n+1)→ℝ, JoinedIn (shiftedSlice P F values h t) y a ∧
      (a ∘ FrozenCoordinateOrdering.permutation F.frozen)∈IntegralMixedSelectedPhysicalFiber.physical
        (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen))
        hm (sweep x F h hh g hg) φ t := by
  have HY:=((Set.ext_iff.mp (shiftedSlice_fiber P F values h hh t) y).mp hy)
  obtain ⟨a,ha,hphys⟩:=exists_component_sample x hm φ F h hh g hg values H t y HY hp
  rw [←shiftedSlice_fiber P F values h hh t] at ha
  exact ⟨a,joinedIn_of_heightCut x hm φ F h hh values H t ht y hy a ha,hphys⟩

theorem regular_path_sample (R : LeanCanny.Encoding.BoundedFullWriter.Readers) (q : List Bool)
    (x : State (LeanCanny.Encoding.BoundedRegularLowModularTerm.source R q) S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame (R.dim q+3))
    (h : Fin (R.dim q+4)) (hh : h∈F.frozen) (g : Fin (R.dim q+4)) (hg : g∉F.frozen)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (ht : (heightCut x hm F h).eval₂ φ.toRingHom t≠0)
    (y : Fin (R.dim q+4)→ℝ)
    (hy : y∈shiftedSlice (LeanCanny.Encoding.BoundedRegularLowModularTerm.source R q) F values h t) :
    ∃ a : Fin (R.dim q+4)→ℝ,
      JoinedIn (shiftedSlice (LeanCanny.Encoding.BoundedRegularLowModularTerm.source R q) F values h t) y a ∧
      (a ∘ FrozenCoordinateOrdering.permutation F.frozen)∈IntegralMixedSelectedPhysicalFiber.physical
        (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen))
        hm (sweep x F h hh g hg) φ t :=
  exists_path_sample x hm φ F h hh g hg values H t ht y hy (regular_source_proper R q)

end LeanCanny.Geometry.IntegralMixedFrozenFrame
