/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedOptionalEndpointCovers
public import LeanCanny.Geometry.IntegralMixedFrozenFrameComponentPaths
/-! # Every point on an actual endpoint fiber is joined to a child-critical point -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedFrozenFrame Set
open IntegralMixedFullHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]
variable {x :State P S B m ι} {F :Frame n} {z :ι→ℝ}
  {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values :Fin m→ℝ} {a b :ℝ}
  {hn :0<n} {hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}

/-- The actual endpoint state gives the recursive path cover and a singular-safe
critical sample in the supplied point's SAME endpoint fiber. -/
theorem PairResult.exists_joined_endpoint_critical (R :PairResult x F z φ values a b hn hcap)
    (h :Fin (n+1)) (hh :h∉F.frozen) (hfirst :h.val=F.frozen.card)
    (g :Fin (n+1)) (hg :g∉insert h F.frozen)
    (charge :ℕ) (hdegree :P.degree=BoundedZeroSource.powerDegree charge)
    (hp :IsProperMap (fun y :Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (room :m+R.commands.length+(n-F.frozen.card)≤S+1) (side :Bool)
    (p :Fin (n+1)→ℝ) (hps :p∈slice P F values) (hph :p h=if side then b else a):
    ∃q :Fin (n+1)→ℝ,JoinedIn (slice P F values∩{y | y h=if side then b else a}) p q ∧
      q∈slice P F values ∧ q h=(if side then b else a) ∧
      ∀i,i∉insert h F.frozen→i≠g→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
          (Int.castRingHom ℝ) q=0:=by
  let endpoint:=if side then R.right else R.left
  let G:=referencedEndpointFrame R.atomic h endpoint
  have HH:h∉R.frame.frozen:=by rw [R.frozen];exact hh
  have Hfirst:h.val=R.frame.frozen.card:=by rw [R.frozen];exact hfirst
  have HG:G.frozen=insert h R.frame.frozen:=rfl
  have Hrank:n+1-G.frozen.card=n-F.frozen.card:=by
    rw [HG,Finset.card_insert_of_notMem HH,R.frozen]
    omega
  have Hroom:m+R.commands.length+(n+1-G.frozen.card)≤S+1:=by rw [Hrank];exact room
  have HU:R.nextValues endpoint=(if side then b else a):=by
    cases side
    · exact R.left_value
    · exact R.right_value
  have HS:slice P G R.nextValues=slice P F values∩{y | y h=if side then b else a}:=by
    rw [referencedEndpointFrame_slice R.atomic h HH endpoint,R.slice_eq,HU]
  have HGfree:g∉G.frozen:=by rw [HG,R.frozen];exact hg
  obtain ⟨q,Hpath,Hslice,Hgrad⟩:=exists_joined_objective_critical
    (continueRun x R.commands R.room) G Hroom
    (R.freeNormal.referencedEndpointFrame R.atomic h endpoint)
    (referencedEndpointFrame_atomic R.atomic h endpoint)
    (R.prefixFrozen.referencedEndpointFrame R.atomic h Hfirst HH endpoint) hn charge hdegree hcap hp
    R.hom R.tuple R.roots R.generators R.nextValues R.quotients g HGfree p
    (by rw [HS];exact ⟨hps,hph⟩)
  rw [HS] at Hpath Hslice
  refine ⟨q,Hpath,Hslice.1,Hslice.2,?_⟩
  intro i hi hig
  apply Hgrad i _ hig
  rw [HG,R.frozen]
  exact hi

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
