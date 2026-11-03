/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedMatchedOptionalAnchorCaptures
/-! # A constant physical point realizes an equal-endpoint midpoint program

This is a direct scale2/refsum construction. It has no open interval,
matched family, Near code, regularity or component-selection premise.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open LeanCanny.Geometry.IntegralMixedFrozenFrame
open IntegralMixedFullHistoryScript IntegralMixedCausalRowConstructor
open IntegralHistorySampler UniformIntegralPowerSchedule FlatAffineCriticalStage Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {F : Frame n} {z : ι→ℝ}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ}
    {c : ℝ} {hn : 0<n}
    {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}

theorem critical_after_freezing (h g : Fin (n+1)) (p : Fin (n+1)→ℝ)
    (HG : ∀i,i∉F.frozen→i≠h→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0) :
    ∀i,i∉insert h F.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0:=by
  intro i hi _
  have HI : i≠h ∧ i∉F.frozen:=by simpa only [Finset.mem_insert,not_or] using hi
  exact HG i HI.2 HI.1

theorem PairResult.exists_degenerate_midpoint_captures
    (R : PairResult x F z φ values c c hn hcap)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (h : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (p : Fin (n+1)→ℝ) (HS : p∈slice P F values) (Hh : p h=c)
    (HG : ∀i,i∉insert h F.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (hp : m+R.commands.length≤S)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen)))
    (room : m+R.commands.length+1+js.length≤S+1) :
    Nonempty (R.MidpointCaptures hp h g j hg hj p js room):=by
  have hh' : h∉R.frame.frozen:=by rw [R.frozen]; exact hh
  have hfirst' : h.val=R.frame.frozen.card:=by rw [R.frozen]; exact hfirst
  have HS' : p∈slice P R.frame R.nextValues:=by rw [R.slice_eq]; exact HS
  have Hh' : p h=(R.nextValues R.left+R.nextValues R.right)/2:=by
    rw [R.left_value,R.right_value,Hh]
    ring
  have HG' : ∀i,i∉insert h R.frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0:=by rw [R.frozen]; exact HG
  obtain ⟨_,HC,y,ψ,hy,hold,hphysical,hrestrict,hψ,hvalues⟩:=
    referenced_midpoint_realize (continueRun x R.commands R.room) hp hn charge hdegree hcap
      R.atomic R.prefixFrozen h hfirst' hh' R.left R.right g j
      (R.free_after_pair h g hg) (R.free_after_pair h j hj)
      R.tuple R.roots R.hom R.generators R.nextValues R.quotients p HS' Hh' HG'
  let frozen:=insert h R.frame.frozen
  let rows:=IntegralMixedPointCompanion.shiftRows (referencedMidpointRows R.atomic h R.left R.right) 1
  have HP : PrefixFrozen (originalFrame frozen (midpointDouble h) rows):=
    (R.prefixFrozen.referencedMidpointFrame R.atomic h hfirst' hh' R.left R.right).retained
  have HS'' : p∈slice P (originalFrame frozen (midpointDouble h) rows) (Fin.cons (p j) R.nextValues):=by
    change p∈slice P (IntegralMixedPointCompanion.frame frozen (midpointDouble h)
      (referencedMidpointRows R.atomic h R.left R.right) 1) (Fin.cons (p j) R.nextValues)
    rw [IntegralMixedPointCompanion.frame_succ,slice_retained]
    exact (Set.ext_iff.mp (referencedMidpointFrame_slice R.atomic h hh' R.left R.right R.nextValues) p).mpr
      ⟨HS',Hh'⟩
  obtain ⟨⟨C⟩,HD⟩:=IntegralMixedPointCompanion.exists_realized
    (R.anchorState hp h g j hg hj) frozen (midpointDouble h) rows ⟨g,R.free_after_pair h g hg⟩
    hn charge hdegree hcap HP y hy ψ hψ (Fin.cons (p j) R.nextValues) hvalues p HS'' HG' js room
  exact ⟨⟨⟨HC,y,ψ,hy,hold,hphysical,hrestrict,hψ,hvalues⟩,C,HD⟩⟩

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
