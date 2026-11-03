/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameFullDescending
public import LeanCanny.Geometry.IntegralMixedFrozenFrameComponentCritical
/-! # A path to an actual critical point in every honest frozen slice

The recursive clopen path cover turns component membership into a path,
including singular slices. Neither a path nor a component cover is supplied.
-/
@[expose] public section
namespace LeanCanny.Connectivity.ClopenPathCover
open Set
variable {X I : Type*} [TopologicalSpace X] {S : Set X}

theorem joinedIn_of_component (C : ClopenPathCover S I) (z y : X)
    (hz : z∈S) (hy : y∈connectedComponentIn S z) : JoinedIn S z y :=by
  obtain ⟨i,HI⟩:=C.imagePiece_cover z hz
  have HC:=C.subset_imagePiece_of_isPreconnected (isPreconnected_connectedComponentIn)
    (connectedComponentIn_subset S z) (mem_connectedComponentIn hz) HI
  exact (C.imagePiece_paths i z HI y (HC hy)).mono (C.imagePiece_subset i)

end LeanCanny.Connectivity.ClopenPathCover
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory
open UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem exists_joined_objective_critical (x : State P S B m ι) (F : Frame n)
    (Hbudget : m+(n+1-F.frozen.card)≤S+1) (HF : FreeNormal F)
    (HA : AtomicRows F m) (HP : PrefixFrozen F) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (z : ι→ℝ)
    (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (h : Fin (n+1)) (hh : h∉F.frozen) (a : Fin (n+1)→ℝ) (ha : a∈slice P F values) :
    ∃ b : Fin (n+1)→ℝ,JoinedIn (slice P F values) a b ∧ b∈slice P F values ∧
      ∀i,i∉F.frozen→i≠h→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
          (Int.castRingHom ℝ) b=0 :=by
  obtain ⟨b,HB,HG⟩:=exists_component_critical_of_proper P F values h hh hp a ha
  obtain ⟨I,_,⟨C⟩⟩:=exists_full_recursive_cover x F Hbudget HF HA HP hn charge hdegree hcap hp φ z hz hφ values H
  exact ⟨b,C.joinedIn_of_component a b ha HB,connectedComponentIn_subset _ _ HB,HG⟩

end LeanCanny.Geometry.IntegralMixedFrozenFrame
