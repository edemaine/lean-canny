/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalGuardedProperLevel
public import LeanCanny.Geometry.IntegralMixedChronologicalRetainedLevel

/-! # Equal endpoint values need only the new child's critical equations

The endpoint specifications and their commands may differ, including two
fresh births at the same height. Their common physical point is captured by
the literal midpoint and both child programs.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedChosenLocalRealization IntegralMixedOptionalEndpoints IntegralMixedPointCompanion
open IntegralMixedFullHistoryScript Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]
variable {x :State P S B m ι} {d :Descriptor n m} {z :ι→ℝ}
  {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values :Fin m→ℝ}
  {hn :0<n} {hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}

private theorem equal_midpoint_captures {a b :ℝ} (F :Frame n)
    (R :PairResult x F z φ values a b hn hcap) (he :a=b)
    (charge :ℕ) (hdegree :P.degree=BoundedZeroSource.powerDegree charge)
    (h :Fin (n+1)) (hfirst :h.val=F.frozen.card) (hh :h∉F.frozen)
    (g j :Fin (n+1)) (hg :g∉(line F h).frozen) (hj :j∉(line F h).frozen)
    (p :Fin (n+1)→ℝ) (HS :p∈slice P F values) (Hh :p h=a)
    (HG :∀i,i∉insert h F.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (hp :m+R.commands.length≤S)
    (js :List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen)))
    (room :m+R.commands.length+1+js.length≤S+1) :
    Nonempty (R.MidpointCaptures hp h g j hg hj p js room):=by
  cases he
  exact R.exists_degenerate_midpoint_captures charge hdegree h hfirst hh g j hg hj p HS Hh HG hp js room

variable {left right :Endpoint m}

/-- No old-objective gradient is required. The midpoint and both children
retain one chosen point on the common endpoint fiber. -/
theorem NativePair.exists_equal_level_captures
    (R :NativePair x d z φ values left right hn hcap)
    (hk :d.labels.length<n+1) (g :Fin (n+1))
    (hg :g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)
    (charge :ℕ) (hdegree :P.degree=BoundedZeroSource.powerDegree charge)
    (he :left.value values=right.value values)
    (p :Fin (n+1)→ℝ) (HS :p∈slice P d.frame values)
    (Hh :p (IntegralMixedChronologicalSweepFrame.next d hk)=left.value values)
    (Hgrad :∀i,i∉insert (IntegralMixedChronologicalSweepFrame.next d hk) d.frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (hp :m+R.result.commands.length≤S)
    (room :m+R.result.commands.length+1+(R.orderedFree hk).length≤S+1)
    (hroom :m+R.result.commands.length+1+(R.orderedFree hk).length≤S)
    (childRoom :m+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length≤S+1) :
    ∃A :R.result.MidpointCaptures hp (IntegralMixedChronologicalSweepFrame.next d hk) g g hg hg
      p (R.orderedFree hk) room,∀side,
      Nonempty (R.LevelChildCaptures hk g hg hp p room A hroom side p childRoom):=by
  let h:=IntegralMixedChronologicalSweepFrame.next d hk
  have hh :h∉d.frame.frozen:=IntegralMixedChronologicalSweepFrame.next_free d hk
  have hfirst :h.val=d.frame.frozen.card:=d.frozen_card.symm
  obtain ⟨A⟩:=equal_midpoint_captures d.frame R.result he charge hdegree h hfirst hh g g hg hg
    p HS Hh Hgrad hp (R.orderedFree hk) room
  refine ⟨A,?_⟩
  intro side
  let current:=R.levelCapturedState hk g hg hp room
  let frozen:=insert h R.result.frame.frozen
  let rows:=R.levelEndpointRows hk side
  let old:=IntegralMixedPointCompanion.values p (Fin.cons (p g) R.result.nextValues) (R.orderedFree hk)
  have HP :PrefixFrozen (R.result.endpointFrame h (R.orderedFree hk).length side):=
    R.result.endpointFrame_prefix h hfirst hh (R.orderedFree hk).length side
  have HS' :p∈slice P (R.result.endpointFrame h (R.orderedFree hk).length side) old:=by
    rw [R.result.endpointFrame_slice h hh p (p g) (R.orderedFree hk) side]
    refine ⟨HS,?_⟩
    cases side
    · exact Hh
    · exact Hh.trans he
  have HG' :∀i,i∉frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0:=by
    dsimp only [frozen]
    rw [R.result.frozen]
    exact Hgrad
  obtain ⟨_,HC,y,ψ,hy,hold,hphysical,hrestrict,hψ,hvalues⟩:=
    HP.real_extend_original_point current hroom hn charge hdegree hcap frozen (fun _=>false) rows
      g g (R.result.free_after_pair h g hg) (R.result.free_after_pair h g hg)
      A.captures.tuple A.captures.roots A.captures.hom A.captures.generators old A.captures.quotients p HS' HG'
  let born:=step current hroom (.critical (R.levelEndpointData hk g hg side).rule)
  let childRows:=IntegralMixedPointCompanion.shiftRows rows 1
  have HP' :PrefixFrozen (originalFrame frozen (fun _=>false) childRows):=HP.retained
  have HS'' :p∈slice P (originalFrame frozen (fun _=>false) childRows) (Fin.cons (p g) old):=by
    change p∈slice P (IntegralMixedPointCompanion.frame frozen (fun _=>false) rows 1) (Fin.cons (p g) old)
    rw [IntegralMixedPointCompanion.frame_succ,slice_retained]
    exact HS'
  obtain ⟨⟨C⟩,HD⟩:=IntegralMixedPointCompanion.exists_realized born frozen (fun _=>false) childRows
    ⟨g,R.result.free_after_pair h g hg⟩ hn charge hdegree hcap HP' y hy ψ hψ
    (Fin.cons (p g) old) hvalues p HS'' HG' (R.orderedFree hk) childRoom
  exact ⟨⟨⟨HC,y,ψ,hy,hold,hphysical,hrestrict,hψ,hvalues⟩,C,HD⟩⟩

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
