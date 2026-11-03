/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedMatchedCapturedEndpointRecord
/-! # The literal optional-pair, midpoint-anchor, captures, endpoint program

The captured point is a member of the same matched family. No independently
chosen branch, replacement source, or fixed endpoint reference is used.
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

theorem PairResult.free_after_pair (R : PairResult x F z φ values a b hn hcap)
    (h g : Fin (n+1)) (hg : g∉(line F h).frozen) : g∉insert h R.frame.frozen:=by
  rw [R.frozen]
  exact hg

noncomputable def PairResult.anchorState (R : PairResult x F z φ values a b hn hcap)
    (hp : m+R.commands.length≤S) (h g j : Fin (n+1))
    (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen) :
    State P S B (m+R.commands.length+1) ((Index ι R.commands⊕Variables (n+1))⊕Unit):=
  criticalStep (continueRun x R.commands R.room) hp
    (referencedMidpointData R.atomic h R.left R.right g j
      (R.free_after_pair h g hg) (R.free_after_pair h j hj)).rule

theorem PairResult.anchor_captures_endpoint_record
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
    (anchorTuple : ((Index ι R.commands⊕Variables (n+1))⊕Unit)→ℝ)
    (anchorHom : (R.anchorState hp h g j hg hj).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen)))
    (room : m+R.commands.length+1+js.length≤S+1)
    (C : IntegralMixedPointCompanion.Realized (R.anchorState hp h g j hg hj)
      (insert h R.frame.frozen) (midpointDouble h)
      (IntegralMixedPointCompanion.shiftRows (referencedMidpointRows R.atomic h R.left R.right) 1)
      ⟨g,R.free_after_pair h g hg⟩ anchorTuple anchorHom
      (Fin.cons ((M.curve i ((a+b)/2)∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm) j) R.nextValues)
      (M.curve i ((a+b)/2)∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm) js room)
    (hroom : m+R.commands.length+1+js.length≤S) (right : Bool) :
    let start:=R.anchorState hp h g j hg hj
    let p:=M.curve i ((a+b)/2)∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm
    let current:=IntegralMixedPointCompanion.run start (insert h R.frame.frozen) (midpointDouble h)
      (IntegralMixedPointCompanion.shiftRows (referencedMidpointRows R.atomic h R.left R.right) 1)
      ⟨g,R.free_after_pair h g hg⟩ js room
    let point:=M.curve i (if right then b else a)∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm
    let E:=R.endpointFrame h js.length right
    let hg' : g∉E.frozen:=by change g∉insert h R.frame.frozen; exact R.free_after_pair h g hg
    let d:=originalPointData E.frozen (fun _=>false)
      (referencedEndpointRows (R.capturedFrame_atomic js.length) h (R.endpointIndex js.length right)) g g hg' hg'
    point∈slice P E (IntegralMixedPointCompanion.values p (Fin.cons (p j) R.nextValues) js) ∧
      d.rule=pointRule E g hg' g hg' ∧
      Nonempty (EndpointRecord current hroom hn hcap d C.tuple C.hom
        (IntegralMixedPointCompanion.values p (Fin.cons (p j) R.nextValues) js) point g) :=by
  exact R.matched_endpoint_record hm charge hdegree HF h hfirst hh g hg H
    ⟨(a+b)/2,by constructor <;> linarith⟩ M i (R.anchorState hp h g j hg hj)
    (insert h R.frame.frozen) (midpointDouble h)
    (IntegralMixedPointCompanion.shiftRows (referencedMidpointRows R.atomic h R.left R.right) 1)
    ⟨g,R.free_after_pair h g hg⟩ anchorTuple anchorHom
    ((M.curve i ((a+b)/2)∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm) j)
    (M.curve i ((a+b)/2)∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm)
    js room C hroom right

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
