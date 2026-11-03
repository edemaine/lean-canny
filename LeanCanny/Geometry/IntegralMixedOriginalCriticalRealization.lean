/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedAtomicFrameRecord
public import LeanCanny.Encoding.IntegralMixedCriticalRecordRealization
/-! # An actual frozen-frame critical point realizes its original record

This is the completeness direction: one supplied physical critical point
constructs a full correlated sample at its exactly encoded pointRule. The
old raw tuple, old hom and retained quotients are preserved together.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralHistorySampler FlatAffineCriticalStage UniformIntegralPowerSchedule Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem AtomicRows.real_extend_point (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (F : Frame n) (HF : AtomicRows F m) (g j : Fin (n+1)) (hg : g∉F.frozen) (hj : j∉F.frozen)
    (z : ι→ℝ) (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : Fin (n+1)→ℝ) (ha : a∈slice P F values)
    (hgrad : ∀i,i∉F.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) a=0) :
    let e:=FrozenCoordinateOrdering.permutation F.frozen
    let Q:=IntegralMixedCoordinateRename.spatial P e
    let xr:=IntegralMixedCoordinateRename.state x e
    let r:=pointRule F g hg j hj
    let code:=(HF.pointData g j hg hj).code
    let c : IntegralMixedFullHistoryScript.Command Q B:=.critical r
    let born:=IntegralMixedFullHistoryScript.step xr hm c
    (IntegralMixedCausalUnitRecordBits.record Q hn m code hcap).template.command
      (commonDenominator x) (commonDenominator_ne_zero x)=c ∧
    ∃y : ((ι⊕Variables (n+1))⊕Unit)→ℝ,∃ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀i,y (Sum.inl (Sum.inl i))=z i) ∧
      (∀i,y (Sum.inl (ambient i))^physical S (2^B) m=a (e i)) ∧
      ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
      (∀i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+1) i) ∧
      ∀i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons (a j) values : Fin (m+1)→ℝ) i:=by
  let e:=FrozenCoordinateOrdering.permutation F.frozen
  let xr:=IntegralMixedCoordinateRename.state x e
  let r:=pointRule F g hg j hj
  let ar:=a ∘ e
  have HY : ar∈actualSlice xr φ (permute F e):=by
    rw [actualSlice_permute]
    change ar ∘ e.symm∈actualSlice x φ F
    rw [actualSlice_eq x φ F values H]
    simpa only [ar,Function.comp_def,Equiv.apply_symm_apply] using ha
  have Hfrozen (i : Fin (n+1)) (hi : i.val<r.offset.val) :
      ((data xr hm r).scales i:ℝ)*ar i=φ (expression xr (r.heights i)):=by
    have HI : i∈(permute F e).frozen:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (FrozenCoordinateOrdering.permutation_mem_iff F.frozen i).mpr hi⟩
    exact HY.2 i HI
  have Hfree : (data xr hm r).free=e.symm g:=by
    apply Fin.ext
    have HB:=(e.symm g).isLt
    have HG : ¬(e.symm g).val<F.frozen.card:=
      fun H=>hg ((FrozenCoordinateOrdering.inverse_mem_iff F.frozen g).mp H)
    change F.frozen.card+((e.symm g).val-F.frozen.card)%(n-F.frozen.card+1)=(e.symm g).val
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have Hgeometry (i : Fin (n+1)) (hi : r.offset.val≤ i.val) (hifree : i≠(data xr hm r).free) :
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial
        (IntegralMixedCoordinateRename.spatial P e).low
        (IntegralMixedCoordinateRename.spatial P e).leading
        (IntegralMixedCoordinateRename.spatial P e).degree)).eval₂ (Int.castRingHom ℝ) ar=0:=by
    have HI : e i∉F.frozen:=by
      intro Hmem
      have HH:=(FrozenCoordinateOrdering.permutation_mem_iff F.frozen i).mp Hmem
      change F.frozen.card≤ i.val at hi
      omega
    have HIG : e i≠g:=by
      intro he
      apply hifree
      exact (e.injective (he.trans (e.apply_symm_apply g).symm)).trans Hfree.symm
    rw [IntegralMixedCoordinateRename.derivative_eval]
    have HA : ar ∘ e.symm=a:=by funext i; exact congrArg a (e.apply_symm_apply i)
    rw [HA]
    exact hgrad (e i) HI HIG
  have Hodd : Odd (P.degree-1):=by
    apply IntegralMixedCriticalRecordConstructor.odd_degree_sub_one
    rw [hdegree]
    exact BoundedZeroSource.powerDegree_even charge
  obtain ⟨y,ψ,hy,hold,hphysical,hrestrict,hψ,hvalues⟩:=criticalStep_real_extend_correlated
    xr hm r Hodd z hz φ hφ values H ar Hfrozen HY.1 Hgeometry
  have Hindex : ar (ClearedCoordinateCritical.freeIndex r.offset.val ((family xr hm r).fit []).le
      ((family xr hm r).coordinate []))=a j:=by
    have HI:=pointRule_index F g hg j hj
    exact (congrArg (fun i=>a (e i)) HI).trans (congrArg a (e.apply_symm_apply j))
  have Hcode : (IntegralMixedCausalUnitRecordBits.record (IntegralMixedCoordinateRename.spatial P e) hn m
      (HF.pointData g j hg hj).code hcap).template.command (commonDenominator x) (commonDenominator_ne_zero x)=
      IntegralMixedFullHistoryScript.Command.critical r:=
    (IntegralMixedCriticalRecordConstructor.command_decode (IntegralMixedCoordinateRename.spatial P e) hn
      (HF.pointData g j hg hj) hcap (commonDenominator x) (commonDenominator_ne_zero x)).trans
      (congrArg (fun t : CriticalRule n=>
        (IntegralMixedFullHistoryScript.Command.critical t : IntegralMixedFullHistoryScript.Command
          (IntegralMixedCoordinateRename.spatial P e) B)) (HF.pointData_rule g j hg hj))
  refine ⟨Hcode,y,ψ,hy,hold,hphysical,hrestrict,hψ,?_⟩
  intro i
  exact (hvalues i).trans (congrArg (fun t=>(Fin.cons t values : Fin (m+1)→ℝ) i) Hindex)

end LeanCanny.Geometry.IntegralMixedFrozenFrame
