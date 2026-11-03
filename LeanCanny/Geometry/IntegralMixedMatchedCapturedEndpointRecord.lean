/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedOptionalCapturedEndpoint
/-! # A matched branch endpoint gives the next physical critical record

Optional endpoints, the midpoint anchor and its coordinate captures are
actual history steps. The endpoint record uses the chosen retained scalar,
at its shifted reference, and keeps the same matched curve and old tuple.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep
open LeanCanny.Geometry.IntegralMixedFrozenFrame
open IntegralMixedFullHistoryScript IntegralMixedCausalRowConstructor IntegralMixedChosenLocalRealization
open IntegralHistorySampler UniformIntegralPowerSchedule FlatAffineCriticalStage Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι κ : Type} [Fintype ι] [Fintype κ]

structure PhysicalEndpointRecord (current : State P S B m κ)
    (born : State P S B (m+1) ((κ⊕Variables (n+1))⊕Unit))
    (embedding : current.sampler.scalarPrefix.carrier→ₐ[ℤ]born.sampler.scalarPrefix.carrier)
    (decoder : Prop)
    (z : κ→ℝ) (φ : current.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (old : Fin m→ℝ) (point : Fin (n+1)→ℝ) (g : Fin (n+1)) where
  decode : decoder
  tuple : ((κ⊕Variables (n+1))⊕Unit)→ℝ
  hom : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ
  roots : ∀i : ((κ⊕Variables (n+1))⊕Unit),
    (born.sampler.rows i).eval₂ (Int.castRingHom ℝ) tuple=0
  old_raw : ∀i : κ,tuple (Sum.inl (Sum.inl i))=z i
  physical : ∀i : Fin (n+1),tuple (Sum.inl (ambient i))^
    UniformIntegralPowerSchedule.physical S (2^B) m=point i
  old_hom : hom.comp embedding=φ
  generators : ∀i : Fin (m+1),hom (born.sampler.scalarPrefix.basis.generator i)=
    tuple (born.sampler.scalar i)^weights S (2^B) (m+1) i
  quotients : ∀i : Fin (m+1),hom (born.bank.numerator i)/
    (born.bank.denominator i:ℝ)=(Fin.cons (point g) old : Fin (m+1)→ℝ) i

abbrev EndpointRecord (current : State P S B m κ) (hm : m≤S) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d : IntegralMixedCriticalRecordConstructor.Data n m)
    (z : κ→ℝ) (φ : current.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (old : Fin m→ℝ) (point : Fin (n+1)→ℝ) (g : Fin (n+1)):=
  PhysicalEndpointRecord current (step current hm (.critical d.rule))
    (scalarLift current hm (.critical d.rule))
    ((IntegralMixedCausalUnitRecordBits.record P hn m d.code hcap).template.command
      (commonDenominator current) (commonDenominator_ne_zero current)=.critical d.rule)
    z φ old point g

variable {x : State P S B m ι} {F : Frame n} {z : ι→ℝ}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ}
    {a b : ℝ} {hn : 0<n}
    {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}

theorem PairResult.matched_endpoint_record
    (R : PairResult x F z φ values a b hn hcap) (hm : m≤S)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (HF : FreeNormal F) (h : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t₀ : Ioo a b)
    (M : MatchedSlabInterior x hm φ (line F h) h (Finset.mem_insert_self h F.frozen)
      g hg values a b t₀)
    (i : IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ t₀.val)
    (start : State P S B (m+R.commands.length+1) κ)
    (captureFrozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row (m+R.commands.length+1))
    (objective : IntegralMixedPointCompanion.Free captureFrozen)
    (anchorTuple : κ→ℝ) (anchorHom : start.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (anchor : ℝ) (p : Fin (n+1)→ℝ)
    (js : List (IntegralMixedPointCompanion.Free captureFrozen))
    (room : m+R.commands.length+1+js.length≤S+1)
    (C : IntegralMixedPointCompanion.Realized start captureFrozen double rows objective
      anchorTuple anchorHom (Fin.cons anchor R.nextValues) p js room)
    (hroom : m+R.commands.length+1+js.length≤S) (right : Bool) :
    let current:=IntegralMixedPointCompanion.run start captureFrozen double rows objective js room
    let point:=M.curve i (if right then b else a)∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm
    let E:=R.endpointFrame h js.length right
    let hg' : g∉E.frozen:=by change g∉insert h R.frame.frozen; rw [R.frozen]; exact hg
    let d:=originalPointData E.frozen (fun _=>false)
      (referencedEndpointRows (R.capturedFrame_atomic js.length) h (R.endpointIndex js.length right)) g g hg' hg'
    point∈slice P E (IntegralMixedPointCompanion.values p (Fin.cons anchor R.nextValues) js) ∧
      d.rule=pointRule E g hg' g hg' ∧
      Nonempty (EndpointRecord current hroom hn hcap d C.tuple C.hom
        (IntegralMixedPointCompanion.values p (Fin.cons anchor R.nextValues) js) point g) :=by
  let endpoint:=if right then b else a
  have HE : endpoint∈Icc a b:=by
    have hab:=t₀.property.1.trans t₀.property.2
    cases right
    · exact ⟨le_rfl,hab.le⟩
    · exact ⟨hab.le,le_rfl⟩
  obtain ⟨HS,Hh,HG⟩:=selected_point_endpoint x hm φ F h hh HF g hg values H endpoint
    (M.curve i endpoint) (M.physical i endpoint HE)
  let point:=M.curve i endpoint∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm
  let E:=R.endpointFrame h js.length right
  let old:=IntegralMixedPointCompanion.values p (Fin.cons anchor R.nextValues) js
  have HP : point∈slice P E old:=by
    rw [R.endpointFrame_slice h hh p anchor js right]
    exact ⟨HS,Hh⟩
  have hg' : g∉E.frozen:=by change g∉insert h R.frame.frozen; rw [R.frozen]; exact hg
  have HG' : ∀j,j∉E.frozen→j≠g→
      (MvPolynomial.pderiv j (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) point=0:=by
    intro j hj hjg
    apply HG j
    · change j∉insert h R.frame.frozen at hj
      rw [R.frozen] at hj
      exact hj
    · exact hjg
  let current:=IntegralMixedPointCompanion.run start captureFrozen double rows objective js room
  obtain ⟨HR,HC,y,ψ,hy,hold,hphys,hrestrict,hψ,hvalues⟩:=
    (R.endpointFrame_prefix h hfirst hh js.length right).real_extend_original_point
      current hroom hn charge hdegree hcap E.frozen (fun _=>false)
      (referencedEndpointRows (R.capturedFrame_atomic js.length) h (R.endpointIndex js.length right))
      g g hg' hg' C.tuple C.roots C.hom C.generators old C.quotients point HP HG'
  exact ⟨HP,HR,⟨⟨HC,y,ψ,hy,hold,hphys,hrestrict,hψ,hvalues⟩⟩⟩

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
