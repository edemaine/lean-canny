/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedPrefixFrame
public import LeanCanny.Geometry.IntegralMixedOriginalFrameRecord
public import LeanCanny.Encoding.IntegralMixedCriticalRecordRealization
/-! # Prefix-frame physical realization for literal scale1/2 row records

Unlike AtomicRows, this accepts a represented two-reference midpoint row.
Every frame and rule is still compiled by the existing original decoder.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralHistorySampler FlatAffineCriticalStage UniformIntegralPowerSchedule Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem PrefixFrozen.real_extend_original_point (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→LeanCanny.Encoding.IntegralMixedCausalRowConstructor.Row m)
    (HPrefix : PrefixFrozen (originalFrame frozen double rows))
    (g j : Fin (n+1)) (hg : g∉frozen) (hj : j∉frozen)
    (z : ι→ℝ) (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : Fin (n+1)→ℝ) (ha : a∈slice P (originalFrame frozen double rows) values)
    (hgrad : ∀i,i∉frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) a=0) :
    let F:=originalFrame frozen double rows
    let d:=originalPointData frozen double rows g j hg hj
    let c : IntegralMixedFullHistoryScript.Command P B:=.critical d.rule
    let born:=IntegralMixedFullHistoryScript.step x hm c
    d.rule=pointRule F g hg j hj ∧
    (IntegralMixedCausalUnitRecordBits.record P hn m d.code hcap).template.command
      (commonDenominator x) (commonDenominator_ne_zero x)=c ∧
    ∃y : ((ι⊕Variables (n+1))⊕Unit)→ℝ,∃ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀i,y (Sum.inl (Sum.inl i))=z i) ∧
      (∀i,y (Sum.inl (ambient i))^physical S (2^B) m=a i) ∧
      ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
      (∀i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+1) i) ∧
      ∀i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons (a j) values : Fin (m+1)→ℝ) i:=by
  let F:=originalFrame frozen double rows
  let d:=originalPointData frozen double rows g j hg hj
  have HD : d.rule=pointRule F g hg j hj:=originalPointData_rule frozen double rows g j hg hj
  have HR (i : Fin (n+1)) : d.rule.heights i=F.heights i:=by
    rw [HD]
    change F.heights (FrozenCoordinateOrdering.permutation F.frozen i)=F.heights i
    rw [HPrefix.permutation]
    rfl
  have HS (i : Fin (n+1)) : d.rule.scales i=F.scales i:=by
    rw [HD]
    change F.scales (FrozenCoordinateOrdering.permutation F.frozen i)=F.scales i
    rw [HPrefix.permutation]
    rfl
  have HA : a∈actualSlice x φ F:=by rw [actualSlice_eq x φ F values H]; exact ha
  have Hfrozen (i : Fin (n+1)) (hi : i.val<d.rule.offset.val) :
      ((data x hm d.rule).scales i:ℝ)*a i=φ (expression x (d.rule.heights i)):=by
    change ((commonDenominator x*d.rule.scales i:ℤ):ℝ)*a i=φ (expression x (d.rule.heights i))
    rw [HS,HR]
    exact HA.2 i ((HPrefix i).mpr hi)
  have Hfree : (data x hm d.rule).free=g:=by
    apply Fin.ext
    change F.frozen.card+(((FrozenCoordinateOrdering.permutation F.frozen).symm g).val-F.frozen.card)%
      (n-F.frozen.card+1)=g.val
    rw [HPrefix.permutation]
    have HB:=g.isLt
    have HG : ¬g.val<F.frozen.card:=fun h=>hg ((HPrefix g).mpr h)
    rw [Nat.mod_eq_of_lt (by change g.val-F.frozen.card<n-F.frozen.card+1; omega)]
    change F.frozen.card+(g.val-F.frozen.card)=g.val
    omega
  have HG (i : Fin (n+1)) (hi : d.rule.offset.val≤ i.val) (hne : i≠(data x hm d.rule).free) :
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) a=0:=by
    apply hgrad i
    · intro hmem
      have HH:=(HPrefix i).mp hmem
      change frozen.card≤ i.val at hi
      change i.val<frozen.card at HH
      omega
    · exact fun he=>hne (he.trans Hfree.symm)
  have Hindex : a (ClearedCoordinateCritical.freeIndex d.rule.offset.val ((family x hm d.rule).fit []).le
      ((family x hm d.rule).coordinate []))=a j:=by
    apply congrArg a
    apply Fin.ext
    change F.frozen.card+(((FrozenCoordinateOrdering.permutation F.frozen).symm j).val-F.frozen.card)%
      (n-F.frozen.card+1)=j.val
    rw [HPrefix.permutation]
    have HB:=j.isLt
    have HJ : ¬j.val<F.frozen.card:=fun h=>hj ((HPrefix j).mpr h)
    rw [Nat.mod_eq_of_lt (by change j.val-F.frozen.card<n-F.frozen.card+1; omega)]
    change F.frozen.card+(j.val-F.frozen.card)=j.val
    omega
  obtain ⟨hcode,y,ψ,hy,hold,hphysical,hrestrict,hψ,hvalues⟩:=
    IntegralMixedCriticalRecordConstructor.real_extend_record x hm hn d charge hdegree hcap
      z hz φ hφ values H a Hfrozen ha.1 HG
  refine ⟨HD,hcode,y,ψ,hy,hold,hphysical,hrestrict,hψ,?_⟩
  intro i
  exact (hvalues i).trans (congrArg (fun t=>(Fin.cons t values : Fin (m+1)→ℝ) i) Hindex)

end LeanCanny.Geometry.IntegralMixedFrozenFrame
