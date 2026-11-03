/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedJointMidpointBranch
public import LeanCanny.Geometry.IntegralMixedReferencedMidpointFrame
/-! # Closed branch endpoints give actual child-frame physical records

The current bank is [anchor,b,a,old]. Its endpoint references are 2 and 1;
reference0 is never treated as a midpoint or endpoint. A fresh endpoint
record retains the entire current sample and selects the free objective g.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι κ : Type} {F : Frame n}

def jointEndpointIndex (m : ℕ) (right : Bool) : Fin (m+3) :=
  if right then ⟨1,by omega⟩ else ⟨2,by omega⟩

noncomputable def jointEndpointFrame (HA : AtomicRows F m) (h : Fin (n+1)) (right : Bool) : Frame n :=
  referencedEndpointFrame HA.retained.retained.retained h (jointEndpointIndex m right)

theorem jointEndpointFrame_height (HA : AtomicRows F m) (h : Fin (n+1)) (right : Bool) :
    (jointEndpointFrame HA h right).heights h=.reference (if right then 1 else 2) :=by
  rw [jointEndpointFrame,referencedEndpointFrame_height]
  cases right <;> rfl

theorem jointEndpointFrame_old_height (HA : AtomicRows F m) (h i : Fin (n+1))
    (right : Bool) (hi : i≠h) :
    (jointEndpointFrame HA h right).heights i=later (later (later (F.heights i))) :=
  referencedEndpointFrame_old_height HA.retained.retained.retained h (jointEndpointIndex m right) i hi

theorem jointEndpointFrame_slice (HA : AtomicRows F m) (h : Fin (n+1)) (hh : h∉F.frozen)
    (right : Bool) (values : Fin m→ℝ) (anchor a b : ℝ) :
    slice P (jointEndpointFrame HA h right) (Fin.cons anchor (Fin.cons b (Fin.cons a values)))=
      slice P F values∩{p | p h=if right then b else a} :=by
  rw [jointEndpointFrame,referencedEndpointFrame_slice HA.retained.retained.retained h hh
      (jointEndpointIndex m right) (Fin.cons anchor (Fin.cons b (Fin.cons a values))),
    slice_retained,slice_retained,slice_retained]
  cases right <;> rfl

theorem jointEndpointFrame_atomic (HA : AtomicRows F m) (h : Fin (n+1)) (right : Bool) :
    AtomicRows (jointEndpointFrame HA h right) (m+3) :=
  referencedEndpointFrame_atomic HA.retained.retained.retained h (jointEndpointIndex m right)

theorem PrefixFrozen.jointEndpointFrame (HP : PrefixFrozen F) (HA : AtomicRows F m)
    (h : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen) (right : Bool) :
    PrefixFrozen (jointEndpointFrame HA h right) :=
  HP.retained.retained.retained.referencedEndpointFrame HA.retained.retained.retained h hfirst hh (jointEndpointIndex m right)

theorem FreeNormal.jointEndpointFrame (HF : FreeNormal F) (HA : AtomicRows F m)
    (h : Fin (n+1)) (right : Bool) : FreeNormal (jointEndpointFrame HA h right) :=
  HF.retained.retained.retained.referencedEndpointFrame HA.retained.retained.retained h (jointEndpointIndex m right)

theorem selected_endpoint_child_point (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (HF : FreeNormal F) (HA : AtomicRows F m)
    (h : Fin (n+1)) (hh : h∉F.frozen) (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (anchor a b : ℝ) (right : Bool) (v : Fin (n+1)→ℝ)
    (hv : v∈IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ (if right then b else a)) :
    let point:=v∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm
    point∈slice P (jointEndpointFrame HA h right) (Fin.cons anchor (Fin.cons b (Fin.cons a values))) ∧
      ∀i,i∉(jointEndpointFrame HA h right).frozen→i≠g→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
          (Int.castRingHom ℝ) point=0 :=by
  obtain ⟨HS,HE,HG⟩:=selected_point_endpoint x hm φ F h hh HF g hg values H _ v hv
  rw [jointEndpointFrame_slice HA h hh right values anchor a b]
  exact ⟨⟨HS,HE⟩,HG⟩

theorem selected_endpoint_critical_height (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (HF : FreeNormal F) (HA : AtomicRows F m)
    (h : Fin (n+1)) (hh : h∉F.frozen) (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (anchor a b : ℝ) (right : Bool) (v : Fin (n+1)→ℝ)
    (hv : v∈IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ (if right then b else a)) :
    (v∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm) g∈
      realCriticalValues P (line (jointEndpointFrame HA h right) g)
        (Fin.cons anchor (Fin.cons b (Fin.cons a values))) g :=by
  obtain ⟨HS,HG⟩:=selected_endpoint_child_point x hm φ HF HA h hh g hg values H anchor a b right v hv
  apply (line_realCriticalValues_iff P (jointEndpointFrame HA h right)
    (Fin.cons anchor (Fin.cons b (Fin.cons a values))) g hg (HF.jointEndpointFrame HA h right) _).mpr
  exact ⟨_,HS,rfl,HG⟩

theorem selected_endpoint_real_extend [Fintype κ]
    (x : State P S B m ι) (hm : m≤S)
    (current : State P S B (m+3) κ) (hroom : m+3≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (HF : FreeNormal F) (HA : AtomicRows F m) (HP : PrefixFrozen F)
    (h : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (anchor a b : ℝ) (right : Bool) (v : Fin (n+1)→ℝ)
    (hv : v∈IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ (if right then b else a))
    (z : κ→ℝ) (hz : ∀i,(current.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (ψ : current.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hψ : ∀i,ψ (current.sampler.scalarPrefix.basis.generator i)=
      z (current.sampler.scalar i)^UniformIntegralPowerSchedule.weights S (2^B) (m+3) i)
    (HN : ∀i,ψ (current.bank.numerator i)/(current.bank.denominator i:ℝ)=
      (Fin.cons anchor (Fin.cons b (Fin.cons a values)) : Fin (m+3)→ℝ) i) :
    let point:=v∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm
    let E:=jointEndpointFrame HA h right
    let d:=originalPointData (insert h F.frozen) (fun _=>false)
      (referencedEndpointRows HA.retained.retained.retained h (jointEndpointIndex m right)) g g hg hg
    let born:=criticalStep current hroom d.rule
    d.rule=pointRule E g hg g hg ∧
    (IntegralMixedCausalUnitRecordBits.record P hn (m+3) d.code hcap).template.command
      (commonDenominator current) (commonDenominator_ne_zero current)=.critical d.rule ∧
    ∃y,∃χ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀i,y (Sum.inl (Sum.inl i))=z i) ∧
      (∀i,y (Sum.inl (FlatAffineCriticalStage.ambient i))^
        UniformIntegralPowerSchedule.physical S (2^B) (m+3)=point i) ∧
      χ.comp (AdjoinRoot.ofAlgHom ℤ _)=ψ ∧
      (∀i,χ (born.sampler.scalarPrefix.basis.generator i)=
        y (born.sampler.scalar i)^UniformIntegralPowerSchedule.weights S (2^B) (m+4) i) ∧
      ∀i,χ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=
        (Fin.cons (point g) (Fin.cons anchor (Fin.cons b (Fin.cons a values))) : Fin (m+4)→ℝ) i :=by
  obtain ⟨HS,HG⟩:=selected_endpoint_child_point x hm φ HF HA h hh g hg values H anchor a b right v hv
  exact (HP.jointEndpointFrame HA h hfirst hh right).real_extend_original_point current hroom hn charge hdegree hcap
    (insert h F.frozen) (fun _=>false)
    (referencedEndpointRows HA.retained.retained.retained h (jointEndpointIndex m right))
    g g hg hg z hz ψ hψ (Fin.cons anchor (Fin.cons b (Fin.cons a values))) HN _ HS HG

theorem branch_endpoint_real_extend [Fintype κ]
    (x : State P S B m ι) (hm : m≤S)
    (current : State P S B (m+3) κ) (hroom : m+3≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (HF : FreeNormal F) (HA : AtomicRows F m) (HP : PrefixFrozen F)
    (h : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (anchor a b : ℝ) (right : Bool) (hab : a≤b) (f : ℝ→Fin (n+1)→ℝ)
    (Hf : ∀t,t∈Icc a b→f t∈IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ t)
    (z : κ→ℝ) (hz : ∀i,(current.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (ψ : current.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hψ : ∀i,ψ (current.sampler.scalarPrefix.basis.generator i)=
      z (current.sampler.scalar i)^UniformIntegralPowerSchedule.weights S (2^B) (m+3) i)
    (HN : ∀i,ψ (current.bank.numerator i)/(current.bank.denominator i:ℝ)=
      (Fin.cons anchor (Fin.cons b (Fin.cons a values)) : Fin (m+3)→ℝ) i) :
    let point:=f (if right then b else a)∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm
    let E:=jointEndpointFrame HA h right
    let d:=originalPointData (insert h F.frozen) (fun _=>false)
      (referencedEndpointRows HA.retained.retained.retained h (jointEndpointIndex m right)) g g hg hg
    let born:=criticalStep current hroom d.rule
    d.rule=pointRule E g hg g hg ∧
    (IntegralMixedCausalUnitRecordBits.record P hn (m+3) d.code hcap).template.command
      (commonDenominator current) (commonDenominator_ne_zero current)=.critical d.rule ∧
    ∃y,∃χ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀i,y (Sum.inl (Sum.inl i))=z i) ∧
      (∀i,y (Sum.inl (FlatAffineCriticalStage.ambient i))^
        UniformIntegralPowerSchedule.physical S (2^B) (m+3)=point i) ∧
      χ.comp (AdjoinRoot.ofAlgHom ℤ _)=ψ ∧
      (∀i,χ (born.sampler.scalarPrefix.basis.generator i)=
        y (born.sampler.scalar i)^UniformIntegralPowerSchedule.weights S (2^B) (m+4) i) ∧
      ∀i,χ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=
        (Fin.cons (point g) (Fin.cons anchor (Fin.cons b (Fin.cons a values))) : Fin (m+4)→ℝ) i :=by
  apply selected_endpoint_real_extend x hm current hroom hn charge hdegree hcap φ HF HA HP h hfirst hh g hg values H
    anchor a b right (f (if right then b else a)) ?_ z hz ψ hψ HN
  apply Hf
  cases right
  · exact ⟨le_rfl,hab⟩
  · exact ⟨hab,le_rfl⟩

end LeanCanny.Geometry.IntegralMixedFrozenFrame
