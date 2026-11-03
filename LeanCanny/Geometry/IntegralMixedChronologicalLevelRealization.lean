/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelCodes

/-! # One matched family realizes the entire proper-slab level at its two endpoints -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Connectivity IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralHistorySampler UniformIntegralPowerSchedule FlatAffineCriticalStage
open IntegralMixedOptionalEndpoints IntegralMixedPointCompanion IntegralMixedFullHistoryScript IntegralMixedChosenLocalRealization Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {d : Descriptor n m} {z : ι→ℝ}
  {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {left right : Endpoint m}
  {hn : 0<n} {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
variable (R : NativePair x d z φ values left right hn hcap) (hk : d.labels.length<n+1)
  (g : Fin (n+1)) (hg : g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)

noncomputable def NativePair.levelCapturedState (hp : m+R.result.commands.length≤S)
    (room : m+R.result.commands.length+1+(R.orderedFree hk).length≤S+1) :=
  IntegralMixedPointCompanion.run (R.result.anchorState hp (IntegralMixedChronologicalSweepFrame.next d hk) g g hg hg)
    (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
    (midpointDouble (IntegralMixedChronologicalSweepFrame.next d hk))
    (shiftRows (R.levelMidpointRows hk) 1) ⟨g,R.result.free_after_pair _ g hg⟩ (R.orderedFree hk) room

abbrev NativePair.LevelChildCaptures (hp : m+R.result.commands.length≤S)
    (p : Fin (n+1)→ℝ) (room : m+R.result.commands.length+1+(R.orderedFree hk).length≤S+1)
    (A : R.result.MidpointCaptures hp (IntegralMixedChronologicalSweepFrame.next d hk) g g hg hg
      p (R.orderedFree hk) room)
    (hroom : m+R.result.commands.length+1+(R.orderedFree hk).length≤S)
    (side : Bool) (endpoint : Fin (n+1)→ℝ)
    (childRoom : m+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length≤S+1) :=
  let current:=R.levelCapturedState hk g hg hp room
  let data:=R.levelEndpointData hk g hg side
  AnchoredCaptures current (step current hroom (.critical data.rule)) (scalarLift current hroom (.critical data.rule))
    ((IntegralMixedCausalUnitRecordBits.record P hn (m+R.result.commands.length+1+(R.orderedFree hk).length)
      data.code hcap).template.command (commonDenominator current) (commonDenominator_ne_zero current)=.critical data.rule)
    (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen) (fun _=>false)
    (shiftRows (R.levelEndpointRows hk side) 1) ⟨g,R.result.free_after_pair _ g hg⟩
    A.captures.tuple A.captures.hom (IntegralMixedPointCompanion.values p (Fin.cons (p g) R.result.nextValues)
      (R.orderedFree hk)) endpoint g (R.orderedFree hk) childRoom hn hcap

theorem NativePair.exists_matched_level_captures (hm : m≤S) (charge : ℕ)
    (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (hab : left.value values<right.value values)
    (M : MatchedSlabInterior x hm φ (line d.frame (IntegralMixedChronologicalSweepFrame.next d hk))
      (IntegralMixedChronologicalSweepFrame.next d hk) (Finset.mem_insert_self _ _) g hg values
      (left.value values) (right.value values) ⟨(left.value values+right.value values)/2,by constructor <;> linarith⟩)
    (i : IntegralMixedSelectedPhysicalFiber.physical (cutSource x d.frame (IntegralMixedChronologicalSweepFrame.next d hk))
      hm (cutRule x d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg) φ ((left.value values+right.value values)/2))
    (hp : m+R.result.commands.length≤S)
    (room : m+R.result.commands.length+1+(R.orderedFree hk).length≤S+1)
    (hroom : m+R.result.commands.length+1+(R.orderedFree hk).length≤S)
    (childRoom : m+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length≤S+1) :
    let e:=FrozenCoordinateOrdering.permutation (line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen
    let p:=M.curve i ((left.value values+right.value values)/2)∘e.symm
    ∃ A : R.result.MidpointCaptures hp (IntegralMixedChronologicalSweepFrame.next d hk) g g hg hg
      p (R.orderedFree hk) room,∀side,
        Nonempty (R.LevelChildCaptures hk g hg hp p room A hroom side
          (M.curve i (if side then right.value values else left.value values)∘e.symm) childRoom) :=by
  let h:=IntegralMixedChronologicalSweepFrame.next d hk
  have hh : h∉d.frame.frozen:=IntegralMixedChronologicalSweepFrame.next_free d hk
  have hfirst : h.val=d.frame.frozen.card:=d.frozen_card.symm
  obtain ⟨A,Hends⟩:=R.result.exists_matched_endpoint_extension hm charge hdegree d.free_normal h hfirst hh
    g g hg hg H hab M i hp (R.orderedFree hk) room hroom
  refine ⟨A,?_⟩
  intro side
  obtain ⟨HS,_,⟨E⟩⟩:=Hends side
  let e:=FrozenCoordinateOrdering.permutation (line d.frame h).frozen
  let p:=M.curve i ((left.value values+right.value values)/2)∘e.symm
  let endpoint:=M.curve i (if side then right.value values else left.value values)∘e.symm
  let frozen:=insert h R.result.frame.frozen
  let rows:=R.levelEndpointRows hk side
  let old:=IntegralMixedPointCompanion.values p (Fin.cons (p g) R.result.nextValues) (R.orderedFree hk)
  have HT : (if side then right.value values else left.value values)∈Icc (left.value values) (right.value values):=by
    cases side
    · exact ⟨le_rfl,hab.le⟩
    · exact ⟨hab.le,le_rfl⟩
  obtain ⟨_,_,HG⟩:=selected_point_endpoint x hm φ d.frame h hh d.free_normal g hg values H _ _ (M.physical i _ HT)
  have HG' : ∀j,j∉frozen→j≠g→
      (MvPolynomial.pderiv j (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) endpoint=0:=by
    dsimp only [frozen]
    rw [R.result.frozen]
    exact HG
  let current:=R.levelCapturedState hk g hg hp room
  let born:=step current hroom (.critical (R.levelEndpointData hk g hg side).rule)
  have HP : PrefixFrozen (R.result.endpointFrame h (R.orderedFree hk).length side):=
    R.result.endpointFrame_prefix h hfirst hh (R.orderedFree hk).length side
  have HP' : PrefixFrozen (originalFrame frozen (fun _=>false) (shiftRows rows 1)):=HP.retained
  have HS' : endpoint∈slice P (originalFrame frozen (fun _=>false) (shiftRows rows 1)) (Fin.cons (endpoint g) old):=by
    change endpoint∈slice P (IntegralMixedPointCompanion.frame frozen (fun _=>false) rows 1) (Fin.cons (endpoint g) old)
    rw [IntegralMixedPointCompanion.frame_succ,slice_retained]
    exact HS
  obtain ⟨⟨C⟩,HD⟩:=IntegralMixedPointCompanion.exists_realized born frozen (fun _=>false) (shiftRows rows 1)
    ⟨g,R.result.free_after_pair h g hg⟩ hn charge hdegree hcap HP' E.tuple E.roots E.hom E.generators
    (Fin.cons (endpoint g) old) E.quotients endpoint HS' HG' (R.orderedFree hk) childRoom
  exact ⟨⟨E,C,HD⟩⟩

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
