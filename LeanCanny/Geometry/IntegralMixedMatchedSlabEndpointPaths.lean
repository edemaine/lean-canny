/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ComponentSlabEndpointPaths
public import LeanCanny.Geometry.IntegralMixedOptionalEndpointCovers
public import LeanCanny.Geometry.IntegralMixedMatchedSlabInterior

/-! # Actual matched branches reduce slab paths to the recursive endpoint fibers

Both the sections and the interior cover come from the SAME matched family.
Endpoint covers are constructed from the actual optional-pair run. The
remaining recursive relation is literal fiber JoinedIn, not a native oracle.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedFrozenFrame Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {F : Frame n} {z : ι→ℝ}
  {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {a b : ℝ}
  {hn : 0<n} {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}

theorem PairResult.matched_endpoint_paths (R : PairResult x F z φ values a b hn hcap)
    (hm : m≤S) (h : Fin (n+1)) (hh : h∉F.frozen) (hfirst : h.val=F.frozen.card)
    (HF : FreeNormal F) (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (room : m+R.commands.length+(n-F.frozen.card)≤S+1) (hab : a<b)
    (t₀ : Ioo a b)
    (M : MatchedSlabInterior x hm φ (line F h) h (Finset.mem_insert_self h F.frozen) g hg values a b t₀)
    (u v : slice P (coarse (line F h) h) values)
    (hu : coarseProjection P (line F h) values h u=a∨coarseProjection P (line F h) values h u=b)
    (hv : coarseProjection P (line F h) values h v=a∨coarseProjection P (line F h) values h v=b) :
    JoinedIn ((coarseProjection P (line F h) values h) ⁻¹' Icc a b) u v ↔
      M.interior.EndpointReach u v :=by
  obtain ⟨L,HL,⟨left⟩⟩:=R.exists_endpoint_cover h hh hfirst HF charge hdegree hp room false
  obtain ⟨R',HR,⟨right⟩⟩:=R.exists_endpoint_cover h hh hfirst HF charge hdegree hp room true
  let : Finite L:=HL
  let : Finite R':=HR
  let : Finite (IntegralMixedSelectedPhysicalFiber.physical
    (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation (line F h).frozen)) hm
    (sweep x (line F h) h (Finset.mem_insert_self h F.frozen) g hg) φ t₀.val):=M.finite_index
  exact M.interior.endpoint_joined_iff_reach left right
    (coarseProjection_continuous P (line F h) values h) hab t₀ M.clopen hu hv

theorem closed_slab_image (P : SpatialSource n) (F : Frame n) (values : Fin m→ℝ)
    (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F) (a b : ℝ) :
    Subtype.val '' ((coarseProjection P (line F h) values h) ⁻¹' Icc a b)=
      slice P F values∩{y | y h∈Icc a b} :=by
  ext y
  constructor
  · rintro ⟨u,hu,rfl⟩
    refine ⟨?_,?_⟩
    · simpa only [coarse_line F h hh] using u.property
    · change projection (line F h) values h u.val∈Icc a b at hu
      rwa [line_projection F h (HF h hh) values u.val] at hu
  · rintro ⟨hy,ht⟩
    let u : slice P (coarse (line F h) h) values:=⟨y,by simpa only [coarse_line F h hh] using hy⟩
    refine ⟨u,?_,rfl⟩
    change projection (line F h) values h y∈Icc a b
    rwa [line_projection F h (HF h hh) values y]

theorem PairResult.matched_endpoint_paths_raw (R : PairResult x F z φ values a b hn hcap)
    (hm : m≤S) (h : Fin (n+1)) (hh : h∉F.frozen) (hfirst : h.val=F.frozen.card)
    (HF : FreeNormal F) (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (room : m+R.commands.length+(n-F.frozen.card)≤S+1) (hab : a<b)
    (t₀ : Ioo a b)
    (M : MatchedSlabInterior x hm φ (line F h) h (Finset.mem_insert_self h F.frozen) g hg values a b t₀)
    (u v : slice P (coarse (line F h) h) values)
    (hu : coarseProjection P (line F h) values h u=a∨coarseProjection P (line F h) values h u=b)
    (hv : coarseProjection P (line F h) values h v=a∨coarseProjection P (line F h) values h v=b) :
    JoinedIn (slice P F values∩{y | y h∈Icc a b}) u.val v.val ↔ M.interior.EndpointReach u v :=by
  have HU : u∈(coarseProjection P (line F h) values h) ⁻¹' Icc a b:=by
    change coarseProjection P (line F h) values h u∈Icc a b
    rcases hu with HE|HE <;> rw [HE] <;> exact ⟨by linarith,by linarith⟩
  have HV : v∈(coarseProjection P (line F h) values h) ⁻¹' Icc a b:=by
    change coarseProjection P (line F h) values h v∈Icc a b
    rcases hv with HE|HE <;> rw [HE] <;> exact ⟨by linarith,by linarith⟩
  have HI:=Topology.IsEmbedding.subtypeVal.isInducing.joinedIn_image HU HV
  rw [closed_slab_image P F values h hh HF a b] at HI
  exact HI.trans (R.matched_endpoint_paths hm h hh hfirst HF g hg charge hdegree hp room hab t₀ M u v hu hv)

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
