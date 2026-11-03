/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedOptionalAnchorEndpointRecord
/-! # Constructing the correlated anchor and captures from one matched branch

This supplies the actual capture object used by the endpoint-record theorem.
The anchor is physically realized at the same matched midpoint, and its
interpretation extends the optional pair's interpretation literally.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep
open LeanCanny.Geometry.IntegralMixedFrozenFrame
open IntegralMixedFullHistoryScript IntegralMixedCausalRowConstructor
open IntegralHistorySampler UniformIntegralPowerSchedule FlatAffineCriticalStage Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {F : Frame n} {z : ι→ℝ}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ}
    {a b : ℝ} {hn : 0<n}
    {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}

structure AnchoredCaptures (before : State P S B m ι)
    (born : State P S B (m+1) ((ι⊕Variables (n+1))⊕Unit))
    (embedding : before.sampler.scalarPrefix.carrier→ₐ[ℤ]born.sampler.scalarPrefix.carrier)
    (decoder : Prop) (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row (m+1)) (objective : IntegralMixedPointCompanion.Free frozen)
    (oldTuple : ι→ℝ) (oldHom : before.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (oldValues : Fin m→ℝ) (point : Fin (n+1)→ℝ) (j : Fin (n+1))
    (js : List (IntegralMixedPointCompanion.Free frozen)) (room : m+1+js.length≤S+1)
    (hn : 0<n) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) where
  anchor : PhysicalEndpointRecord before born embedding decoder oldTuple oldHom oldValues point j
  captures : IntegralMixedPointCompanion.Realized born frozen double rows objective
    anchor.tuple anchor.hom (Fin.cons (point j) oldValues) point js room
  captures_decode : IntegralMixedPointCompanion.Decoded born frozen double rows objective hn hcap js room

abbrev PairResult.MidpointCaptures (R : PairResult x F z φ values a b hn hcap)
    (hp : m+R.commands.length≤S) (h g j : Fin (n+1))
    (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (point : Fin (n+1)→ℝ)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen)))
    (room : m+R.commands.length+1+js.length≤S+1):=
  let d:=referencedMidpointData R.atomic h R.left R.right g j
    (R.free_after_pair h g hg) (R.free_after_pair h j hj)
  AnchoredCaptures (continueRun x R.commands R.room) (R.anchorState hp h g j hg hj)
    (IntegralMixedChosenLocalRealization.scalarLift (continueRun x R.commands R.room) hp (.critical d.rule))
    ((IntegralMixedCausalUnitRecordBits.record P hn (m+R.commands.length) d.code hcap).template.command
      (commonDenominator (continueRun x R.commands R.room)) (commonDenominator_ne_zero _)=.critical d.rule)
    (insert h R.frame.frozen) (midpointDouble h)
    (IntegralMixedPointCompanion.shiftRows (referencedMidpointRows R.atomic h R.left R.right) 1)
    ⟨g,R.free_after_pair h g hg⟩ R.tuple R.hom R.nextValues point j js room hn hcap

theorem PairResult.exists_matched_midpoint_captures
    (R : PairResult x F z φ values a b hn hcap) (hm : m≤S)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (HF : FreeNormal F) (h : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (hab : a<b)
    (M : MatchedSlabInterior x hm φ (line F h) h (Finset.mem_insert_self h F.frozen)
      g hg values a b ⟨(a+b)/2,by constructor <;> linarith⟩)
    (i : IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm
      (cutRule x F h g hg) φ ((a+b)/2))
    (hp : m+R.commands.length≤S)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen)))
    (room : m+R.commands.length+1+js.length≤S+1) :
    Nonempty (R.MidpointCaptures hp h g j hg hj
      (M.curve i ((a+b)/2)∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm) js room) :=by
  let mid:=(a+b)/2
  let point:=M.curve i mid∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm
  have hmid : mid∈Icc a b:=by constructor <;> dsimp only [mid] <;> linarith
  obtain ⟨HS,Hh,HG⟩:=selected_point_endpoint x hm φ F h hh HF g hg values H mid
    (M.curve i mid) (M.physical i mid hmid)
  have hh' : h∉R.frame.frozen:=by rw [R.frozen]; exact hh
  have hfirst' : h.val=R.frame.frozen.card:=by rw [R.frozen]; exact hfirst
  have HS' : point∈slice P R.frame R.nextValues:=by rw [R.slice_eq]; exact HS
  have Hh' : point h=(R.nextValues R.left+R.nextValues R.right)/2:=by
    rw [R.left_value,R.right_value]
    exact Hh
  have HG' : ∀k,k∉insert h R.frame.frozen→k≠g→
      (MvPolynomial.pderiv k (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) point=0:=by rw [R.frozen]; exact HG
  obtain ⟨_,HC,y,ψ,hy,hold,hphysical,hrestrict,hψ,hvalues⟩:=
    referenced_midpoint_realize (continueRun x R.commands R.room) hp hn charge hdegree hcap
      R.atomic R.prefixFrozen h hfirst' hh' R.left R.right g j
      (R.free_after_pair h g hg) (R.free_after_pair h j hj)
      R.tuple R.roots R.hom R.generators R.nextValues R.quotients point HS' Hh' HG'
  let frozen:=insert h R.frame.frozen
  let rows:=IntegralMixedPointCompanion.shiftRows (referencedMidpointRows R.atomic h R.left R.right) 1
  have HP : PrefixFrozen (originalFrame frozen (midpointDouble h) rows):=
    (R.prefixFrozen.referencedMidpointFrame R.atomic h hfirst' hh' R.left R.right).retained
  have HS'' : point∈slice P (originalFrame frozen (midpointDouble h) rows)
      (Fin.cons (point j) R.nextValues):=by
    change point∈slice P (IntegralMixedPointCompanion.frame frozen (midpointDouble h)
      (referencedMidpointRows R.atomic h R.left R.right) 1) (Fin.cons (point j) R.nextValues)
    rw [IntegralMixedPointCompanion.frame_succ,slice_retained]
    exact (Set.ext_iff.mp (referencedMidpointFrame_slice R.atomic h hh' R.left R.right R.nextValues) point).mpr
      ⟨HS',Hh'⟩
  obtain ⟨⟨C⟩,HD⟩:=IntegralMixedPointCompanion.exists_realized
    (R.anchorState hp h g j hg hj) frozen (midpointDouble h) rows ⟨g,R.free_after_pair h g hg⟩
    hn charge hdegree hcap HP y hy ψ hψ (Fin.cons (point j) R.nextValues) hvalues point HS'' HG' js room
  exact ⟨⟨⟨HC,y,ψ,hy,hold,hphysical,hrestrict,hψ,hvalues⟩,C,HD⟩⟩

theorem PairResult.exists_matched_endpoint_extension
    (R : PairResult x F z φ values a b hn hcap) (hm : m≤S)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (HF : FreeNormal F) (h : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (hab : a<b)
    (M : MatchedSlabInterior x hm φ (line F h) h (Finset.mem_insert_self h F.frozen)
      g hg values a b ⟨(a+b)/2,by constructor <;> linarith⟩)
    (i : IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm
      (cutRule x F h g hg) φ ((a+b)/2))
    (hp : m+R.commands.length≤S)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen)))
    (room : m+R.commands.length+1+js.length≤S+1)
    (hroom : m+R.commands.length+1+js.length≤S) :
    let p:=M.curve i ((a+b)/2)∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm
    ∃ A : R.MidpointCaptures hp h g j hg hj p js room,∀ right,
      let current:=IntegralMixedPointCompanion.run (R.anchorState hp h g j hg hj)
        (insert h R.frame.frozen) (midpointDouble h)
        (IntegralMixedPointCompanion.shiftRows (referencedMidpointRows R.atomic h R.left R.right) 1)
        ⟨g,R.free_after_pair h g hg⟩ js room
      let point:=M.curve i (if right then b else a)∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm
      let E:=R.endpointFrame h js.length right
      let hg' : g∉E.frozen:=by change g∉insert h R.frame.frozen; exact R.free_after_pair h g hg
      let d:=originalPointData E.frozen (fun _=>false)
        (referencedEndpointRows (R.capturedFrame_atomic js.length) h (R.endpointIndex js.length right)) g g hg' hg'
      point∈slice P E (IntegralMixedPointCompanion.values p (Fin.cons (p j) R.nextValues) js) ∧
        d.rule=pointRule E g hg' g hg' ∧
        Nonempty (EndpointRecord current hroom hn hcap d A.captures.tuple A.captures.hom
          (IntegralMixedPointCompanion.values p (Fin.cons (p j) R.nextValues) js) point g) :=by
  obtain ⟨A⟩:=R.exists_matched_midpoint_captures hm charge hdegree HF h hfirst hh g j hg hj H hab M i hp js room
  refine ⟨A,?_⟩
  intro right
  exact R.anchor_captures_endpoint_record hm charge hdegree HF h hfirst hh g j hg hj H hab M i hp
    A.anchor.tuple A.anchor.hom js room A.captures hroom right

theorem PairResult.MidpointCaptures.original_raw
    (R : PairResult x F z φ values a b hn hcap) (hp : m+R.commands.length≤S)
    (h g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (point : Fin (n+1)→ℝ) (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen)))
    (room : m+R.commands.length+1+js.length≤S+1)
    (A : R.MidpointCaptures hp h g j hg hj point js room) (i : ι) :
    A.anchor.tuple (Sum.inl (Sum.inl (oldColumns R.commands i)))=z i:=
  (A.anchor.old_raw _).trans (R.old_raw i)

theorem PairResult.MidpointCaptures.original_hom
    (R : PairResult x F z φ values a b hn hcap) (hp : m+R.commands.length≤S)
    (h g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (point : Fin (n+1)→ℝ) (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen)))
    (room : m+R.commands.length+1+js.length≤S+1)
    (A : R.MidpointCaptures hp h g j hg hj point js room) :
    (A.anchor.hom.comp (IntegralMixedChosenLocalRealization.scalarLift
      (continueRun x R.commands R.room) hp (.critical
        (referencedMidpointData R.atomic h R.left R.right g j
          (R.free_after_pair h g hg) (R.free_after_pair h j hj)).rule))).comp
      (oldLift x R.commands R.room)=φ:=by
  rw [A.anchor.old_hom]
  exact R.old_hom

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
