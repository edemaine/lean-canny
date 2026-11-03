/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedReferencedMidpointFrame
public import LeanCanny.Geometry.IntegralMixedPrefixOriginalPointRealization
public import LeanCanny.Encoding.IntegralMixedChosenCutRecordBounds
public import LeanCanny.Geometry.IntegralMixedCriticalReadback
/-! # Arbitrary retained midpoint references compile and read back literally -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralHistorySampler UniformIntegralPowerSchedule FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} {F : Frame n}

noncomputable def referencedMidpointData (HA : AtomicRows F m) (h : Fin (n+1)) (u v : Fin m)
    (g j : Fin (n+1)) (hg : g∉insert h F.frozen) (hj : j∉insert h F.frozen) :=
  originalPointData (insert h F.frozen) (midpointDouble h) (referencedMidpointRows HA h u v) g j hg hj

variable [Fintype ι]

theorem referenced_midpoint_realize (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (HA : AtomicRows F m) (HP : PrefixFrozen F) (h : Fin (n+1))
    (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen) (u v : Fin m)
    (g j : Fin (n+1)) (hg : g∉insert h F.frozen) (hj : j∉insert h F.frozen)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (point : Fin (n+1)→ℝ) (hp : point∈slice P F values) (hmid : point h=(values u+values v)/2)
    (hgrad : ∀ i,i∉insert h F.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) point=0) :
    let d:=referencedMidpointData HA h u v g j hg hj
    let born:=criticalStep x hm d.rule
    d.code.length≤IntegralMixedCutRecordConstructor.codeBudget n m B ∧
    (IntegralMixedCausalUnitRecordBits.record P hn m d.code hcap).template.command
      (commonDenominator x) (commonDenominator_ne_zero x)=.critical d.rule ∧
    ∃ y : ((ι⊕Variables (n+1))⊕Unit)→ℝ,∃ ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀ i,y (Sum.inl (Sum.inl i))=z i) ∧
      (∀ i,y (Sum.inl (ambient i))^physical S (2^B) m=point i) ∧
      ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
      (∀ i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+1) i) ∧
      ∀ i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons (point j) values : Fin (m+1)→ℝ) i :=by
  have HM : point∈slice P (referencedMidpointFrame HA h u v) values:=by
    rw [referencedMidpointFrame_slice HA h hh u v values]
    exact ⟨hp,hmid⟩
  obtain ⟨_,hcode,y,ψ,hy,hold,hphysical,hrestrict,hψ,Hvalues⟩:=
    (HP.referencedMidpointFrame HA h hfirst hh u v).real_extend_original_point x hm hn charge hdegree hcap
      (insert h F.frozen) (midpointDouble h) (referencedMidpointRows HA h u v) g j hg hj
      z hz φ hφ values H point HM hgrad
  exact ⟨(referencedMidpointData HA h u v g j hg hj).code_length.trans
    (IntegralMixedCutRecordConstructor.critical_codeBudget_le n m B),hcode,y,ψ,hy,hold,hphysical,hrestrict,hψ,Hvalues⟩

omit [Fintype ι] in
theorem referenced_midpoint_sound (x : State P S B m ι) (hm : m≤S)
    (HA : AtomicRows F m) (HP : PrefixFrozen F) (h : Fin (n+1))
    (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen) (u v : Fin m)
    (g j : Fin (n+1)) (hg : g∉insert h F.frozen) (hj : j∉insert h F.frozen)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (point : Fin (n+1)→ℝ)
    (HC : IntegralMixedCriticalReadback.CriticalPoint x hm (referencedMidpointData HA h u v g j hg hj).rule φ point) :
    point∈slice P F values ∧ point h=(values u+values v)/2 :=by
  let M:=referencedMidpointFrame HA h u v
  let d:=referencedMidpointData HA h u v g j hg hj
  have HM:=HP.referencedMidpointFrame HA h hfirst hh u v
  have HR (i : Fin (n+1)) : d.rule.heights i=M.heights i:=by
    change (referencedMidpointRows HA h u v (FrozenCoordinateOrdering.permutation M.frozen i)).value=
      (referencedMidpointRows HA h u v i).value
    rw [HM.permutation]
    rfl
  have HS (i : Fin (n+1)) : d.rule.scales i=M.scales i:=by
    change (if midpointDouble h (FrozenCoordinateOrdering.permutation M.frozen i) then 2 else 1)=_
    rw [HM.permutation]
    rfl
  have HT : point∈actualSlice x φ M:=by
    refine ⟨HC.1,?_⟩
    intro i hi
    have HI:=HC.2.1 i ((HM i).mp hi)
    change ((commonDenominator x*d.rule.scales i:ℤ):ℝ)*point i=φ (expression x (d.rule.heights i)) at HI
    rw [HS,HR] at HI
    exact HI
  rw [actualSlice_eq x φ M values H] at HT
  exact (Set.ext_iff.mp (referencedMidpointFrame_slice HA h hh u v values) point).mp HT

end LeanCanny.Geometry.IntegralMixedFrozenFrame
