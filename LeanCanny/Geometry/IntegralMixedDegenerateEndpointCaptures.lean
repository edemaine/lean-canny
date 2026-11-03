/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedDegenerateMidpointCaptures
/-! # The equal-endpoint child record and its captures keep the same point -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open LeanCanny.Geometry.IntegralMixedFrozenFrame
open IntegralMixedFullHistoryScript IntegralMixedCausalRowConstructor IntegralMixedChosenLocalRealization
open IntegralHistorySampler UniformIntegralPowerSchedule FlatAffineCriticalStage Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {F : Frame n} {z : ι→ℝ}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ}
    {c : ℝ} {hn : 0<n}
    {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}

noncomputable def PairResult.capturedState (R : PairResult x F z φ values c c hn hcap)
    (hp : m+R.commands.length≤S) (h g j : Fin (n+1))
    (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen)))
    (room : m+R.commands.length+1+js.length≤S+1):=
  IntegralMixedPointCompanion.run (R.anchorState hp h g j hg hj)
    (insert h R.frame.frozen) (midpointDouble h)
    (IntegralMixedPointCompanion.shiftRows (referencedMidpointRows R.atomic h R.left R.right) 1)
    ⟨g,R.free_after_pair h g hg⟩ js room

noncomputable def PairResult.endpointData (R : PairResult x F z φ values c c hn hcap)
    (h g : Fin (n+1)) (hg : g∉(line F h).frozen) (q : ℕ) (right : Bool):=
  originalPointData (insert h R.frame.frozen) (fun _=>false)
    (referencedEndpointRows (R.capturedFrame_atomic q) h (R.endpointIndex q right))
    g g (R.free_after_pair h g hg) (R.free_after_pair h g hg)

abbrev PairResult.ChildCaptures (R : PairResult x F z φ values c c hn hcap)
    (hp : m+R.commands.length≤S) (h g j : Fin (n+1))
    (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (p : Fin (n+1)→ℝ) (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen)))
    (room : m+R.commands.length+1+js.length≤S+1)
    (A : R.MidpointCaptures hp h g j hg hj p js room)
    (hroom : m+R.commands.length+1+js.length≤S) (right : Bool)
    (childRoom : m+R.commands.length+1+js.length+1+js.length≤S+1):=
  let current:=R.capturedState hp h g j hg hj js room
  let d:=R.endpointData h g hg js.length right
  AnchoredCaptures current (step current hroom (.critical d.rule))
    (scalarLift current hroom (.critical d.rule))
    ((IntegralMixedCausalUnitRecordBits.record P hn (m+R.commands.length+1+js.length) d.code hcap).template.command
      (commonDenominator current) (commonDenominator_ne_zero current)=.critical d.rule)
    (insert h R.frame.frozen) (fun _=>false)
    (IntegralMixedPointCompanion.shiftRows
      (referencedEndpointRows (R.capturedFrame_atomic js.length) h (R.endpointIndex js.length right)) 1)
    ⟨g,R.free_after_pair h g hg⟩ A.captures.tuple A.captures.hom
    (IntegralMixedPointCompanion.values p (Fin.cons (p j) R.nextValues) js) p g js childRoom hn hcap

theorem PairResult.exists_degenerate_child_captures
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
    (room : m+R.commands.length+1+js.length≤S+1)
    (A : R.MidpointCaptures hp h g j hg hj p js room)
    (hroom : m+R.commands.length+1+js.length≤S) (right : Bool)
    (childRoom : m+R.commands.length+1+js.length+1+js.length≤S+1) :
    Nonempty (R.ChildCaptures hp h g j hg hj p js room A hroom right childRoom):=by
  let current:=R.capturedState hp h g j hg hj js room
  let frozen:=insert h R.frame.frozen
  let rows:=referencedEndpointRows (R.capturedFrame_atomic js.length) h (R.endpointIndex js.length right)
  let old:=IntegralMixedPointCompanion.values p (Fin.cons (p j) R.nextValues) js
  let E:=R.endpointFrame h js.length right
  have HP : PrefixFrozen E:=R.endpointFrame_prefix h hfirst hh js.length right
  have HS' : p∈slice P E old:=by
    rw [R.endpointFrame_slice h hh p (p j) js right]
    refine ⟨HS,?_⟩
    change p h=(if right then c else c)
    simpa only [ite_self] using Hh
  have HG' : ∀i,i∉frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0:=by dsimp only [frozen]; rw [R.frozen]; exact HG
  obtain ⟨_,HC,y,ψ,hy,hold,hphysical,hrestrict,hψ,hvalues⟩:=
    HP.real_extend_original_point current hroom hn charge hdegree hcap frozen (fun _=>false) rows
      g g (R.free_after_pair h g hg) (R.free_after_pair h g hg)
      A.captures.tuple A.captures.roots A.captures.hom A.captures.generators old A.captures.quotients p HS' HG'
  let born:=step current hroom (.critical (R.endpointData h g hg js.length right).rule)
  let childRows:=IntegralMixedPointCompanion.shiftRows rows 1
  have HP' : PrefixFrozen (originalFrame frozen (fun _=>false) childRows):=HP.retained
  have HS'' : p∈slice P (originalFrame frozen (fun _=>false) childRows) (Fin.cons (p g) old):=by
    change p∈slice P (IntegralMixedPointCompanion.frame frozen (fun _=>false) rows 1) (Fin.cons (p g) old)
    rw [IntegralMixedPointCompanion.frame_succ,slice_retained]
    exact HS'
  obtain ⟨⟨C⟩,HD⟩:=IntegralMixedPointCompanion.exists_realized born frozen (fun _=>false) childRows
    ⟨g,R.free_after_pair h g hg⟩ hn charge hdegree hcap HP' y hy ψ hψ (Fin.cons (p g) old) hvalues
    p HS'' HG' js childRoom
  exact ⟨⟨⟨HC,y,ψ,hy,hold,hphysical,hrestrict,hψ,hvalues⟩,C,HD⟩⟩

theorem PairResult.exists_degenerate_program
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
    (room : m+R.commands.length+1+js.length≤S+1)
    (hroom : m+R.commands.length+1+js.length≤S)
    (childRoom : m+R.commands.length+1+js.length+1+js.length≤S+1) :
    ∃A : R.MidpointCaptures hp h g j hg hj p js room,∀right,
      Nonempty (R.ChildCaptures hp h g j hg hj p js room A hroom right childRoom):=by
  obtain ⟨A⟩:=R.exists_degenerate_midpoint_captures charge hdegree h hfirst hh g j hg hj p HS Hh HG hp js room
  exact ⟨A,fun right=>R.exists_degenerate_child_captures charge hdegree h hfirst hh g j hg hj p HS Hh HG
    hp js room A hroom right childRoom⟩

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
