/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ComponentSlabAtomicEndpointPaths
public import LeanCanny.Geometry.IntegralMixedMatchedSlabEndpointPaths

/-! # A matched slab needs only its actual branch endpoints as intermediate points

The finite geometric point graph has fiber-path edges and paired-branch
edges. Its native history certificates and fiber recursion remain separate.
-/
@[expose] public section
namespace LeanCanny.Connectivity.ComponentSlabCover.InteriorData
open Set
variable {X J : Type*} [TopologicalSpace X] {p : X→ℝ} {a b : ℝ}

def endpointSupport (D : InteriorData p a b J) (x y : X) : Set X :=
  insert x (insert y (range (fun j=>D.arc j a)∪range (fun j=>D.arc j b)))

theorem endpointSupport_finite [Finite J] (D : InteriorData p a b J) (x y : X) :
    (D.endpointSupport x y).Finite :=
  ((finite_range (fun j=>D.arc j a)).union (finite_range (fun j=>D.arc j b))).insert y |>.insert x

theorem endpointReach_support (D : InteriorData p a b J) (hab : a<b) {x y : X}
    (hy : p y=a∨p y=b) : EndpointReach D x y ↔
      AtomicEndpointReach D (D.endpointSupport x y) ⟨x,mem_insert _ _⟩
        ⟨y,mem_insert_of_mem _ (mem_insert _ _)⟩ :=by
  refine (D.atomicEndpointReach_iff hab (D.endpointSupport x y) ?_ ?_
    ⟨x,mem_insert _ _⟩ ⟨y,mem_insert_of_mem _ (mem_insert _ _)⟩ hy).symm
  · intro j
    exact mem_insert_of_mem _ (mem_insert_of_mem _ (Or.inl ⟨j,rfl⟩))
  · intro j
    exact mem_insert_of_mem _ (mem_insert_of_mem _ (Or.inr ⟨j,rfl⟩))

end LeanCanny.Connectivity.ComponentSlabCover.InteriorData

namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedFrozenFrame Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {F : Frame n} {z : ι→ℝ}
  {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {a b : ℝ}
  {hn : 0<n} {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}

theorem PairResult.matched_atomic_paths (R : PairResult x F z φ values a b hn hcap)
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
    JoinedIn (slice P F values∩{y | y h∈Icc a b}) u.val v.val ↔
      M.interior.AtomicEndpointReach (M.interior.endpointSupport u v)
        ⟨u,mem_insert _ _⟩ ⟨v,mem_insert_of_mem _ (mem_insert _ _)⟩ :=
  (R.matched_endpoint_paths_raw hm h hh hfirst HF g hg charge hdegree hp room hab t₀ M u v hu hv).trans
    (M.interior.endpointReach_support hab hv)

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
