/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameFullDescending
public import LeanCanny.Geometry.IntegralMixedOptionalCapturedEndpoint

/-! # Actual optional endpoint states supply the recursive fiber covers

The covers are derived from the retained tuple, hom, rows and bank values
of the actual pair result. No endpoint component cover is an input.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedFrozenFrame Set
open IntegralMixedFullHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {F : Frame n} {z : ι→ℝ}
  {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {a b : ℝ}
  {hn : 0<n} {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}

 theorem PairResult.exists_endpoint_cover (R : PairResult x F z φ values a b hn hcap)
    (h : Fin (n+1)) (hh : h∉F.frozen) (hfirst : h.val=F.frozen.card) (HF : FreeNormal F)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (room : m+R.commands.length+(n-F.frozen.card)≤S+1) (side : Bool) :
    ∃I : Type,Finite I ∧ Nonempty (ClopenPathCover
      ((coarseProjection P (line F h) values h) ⁻¹' {if side then b else a}) I) :=by
  let u:=if side then R.right else R.left
  let G:=referencedEndpointFrame R.atomic h u
  have HH : h∉R.frame.frozen:=by rw [R.frozen];exact hh
  have Hfirst : h.val=R.frame.frozen.card:=by rw [R.frozen];exact hfirst
  have HG : G.frozen=insert h R.frame.frozen:=rfl
  have Hrank : n+1-G.frozen.card=n-F.frozen.card:=by
    rw [HG,Finset.card_insert_of_notMem HH,R.frozen]
    omega
  have Hroom : m+R.commands.length+(n+1-G.frozen.card)≤S+1:=by rw [Hrank];exact room
  obtain ⟨I,HI,⟨C⟩⟩:=exists_full_recursive_cover
    (continueRun x R.commands R.room) G Hroom
    (R.freeNormal.referencedEndpointFrame R.atomic h u)
    (referencedEndpointFrame_atomic R.atomic h u)
    (R.prefixFrozen.referencedEndpointFrame R.atomic h Hfirst HH u) hn charge hdegree hcap hp
    R.hom R.tuple R.roots R.generators R.nextValues R.quotients
  have HU : R.nextValues u=(if side then b else a):=by
    cases side
    · exact R.left_value
    · exact R.right_value
  have HS : slice P G R.nextValues=shiftedSlice P (line F h) values h (if side then b else a):=by
    rw [line_slice P F h hh HF,referencedEndpointFrame_slice R.atomic h HH u,R.slice_eq,HU]
  let e:=(fiberHomeomorph P (line F h) values h (Finset.mem_insert_self h F.frozen)
    (if side then b else a)).trans (Homeomorph.setCongr HS.symm)
  exact ⟨I,HI,⟨C.comap e⟩⟩

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
