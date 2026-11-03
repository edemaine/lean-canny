/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedPointCompanionLayout
/-! # One physical point realizes every chosen coordinate companion

Every appended block has the same geometric point, not just one common
selected coordinate. Original full tuples and scalar interpretations persist.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedPointCompanion
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralMixedFullHistoryScript IntegralMixedCausalRowConstructor
open IntegralMixedFrozenFrame IntegralMixedChosenLocalRealization
open IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable (x : State P S B m ι) (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen)

noncomputable def lift : (js : List (Free frozen))→(room : m+js.length≤S+1)→
    x.sampler.scalarPrefix.carrier→ₐ[ℤ](run x frozen double rows g js room).sampler.scalarPrefix.carrier
  | [],_=>AlgHom.id ℤ _
  | j::js,room=>(scalarLift (run x frozen double rows g js (by simp only [List.length_cons] at room;omega))
      (by simp only [List.length_cons] at room;omega) (command frozen double rows g js.length j)).comp
        (lift js (by simp only [List.length_cons] at room;omega))

noncomputable def Decoded (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) :
    (js : List (Free frozen))→(room : m+js.length≤S+1)→Prop
  | [],_=>True
  | j::js,room=>Decoded hn hcap js (by simp only [List.length_cons] at room;omega) ∧
      (IntegralMixedCausalUnitRecordBits.record P hn (m+js.length)
        (pointData frozen double rows g js.length j).code hcap).template.command
          (commonDenominator (run x frozen double rows g js (by simp only [List.length_cons] at room;omega)))
          (commonDenominator_ne_zero _)=command frozen double rows g js.length j

structure Realized (z : ι→ℝ) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (old : Fin m→ℝ) (p : Fin (n+1)→ℝ) (js : List (Free frozen)) (room : m+js.length≤S+1) where
  tuple : Index ι (commands (P:=P) (B:=B) frozen double rows g js)→ℝ
  hom : (run x frozen double rows g js room).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ
  roots : ∀i,((run x frozen double rows g js room).sampler.rows i).eval₂ (Int.castRingHom ℝ) tuple=0
  old_raw : ∀i,tuple (IntegralMixedOptionalEndpoints.oldColumns (commands frozen double rows g js) i)=z i
  old_hom : hom.comp (lift x frozen double rows g js room)=φ
  generators : ∀i,hom ((run x frozen double rows g js room).sampler.scalarPrefix.basis.generator i)=
    tuple ((run x frozen double rows g js room).sampler.scalar i)^weights S (2^B) (m+js.length) i
  quotients : ∀i,hom ((run x frozen double rows g js room).bank.numerator i)/
    ((run x frozen double rows g js room).bank.denominator i:ℝ)=values p old js i
  blocks : ∀k : Fin js.length,∀i,tuple (blockColumn frozen double rows g js k i)^
    physical S (2^B) (m+(js.length-1-k.val))=p i

 theorem slice_values (p : Fin (n+1)→ℝ) (old : Fin m→ℝ) (js : List (Free frozen)) :
    slice P (frame frozen double rows js.length) (values p old js)=
      slice P (originalFrame frozen double rows) old :=by
  induction js with
  | nil=>rfl
  | cons j js ih=>
    change slice P (frame frozen double rows (js.length+1)) (Fin.cons (p j.val) (values p old js))=_
    rw [slice_succ,ih]

theorem exists_realized (hn : 0<n) (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (HP : PrefixFrozen (originalFrame frozen double rows))
    (z : ι→ℝ) (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (old : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=old i)
    (p : Fin (n+1)→ℝ) (hp : p∈slice P (originalFrame frozen double rows) old)
    (hg : ∀i,i∉frozen→i≠g.val→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (js : List (Free frozen)) (room : m+js.length≤S+1) :
    Nonempty (Realized x frozen double rows g z φ old p js room) ∧
      Decoded x frozen double rows g hn hcap js room :=by
  induction js with
  | nil=>exact ⟨⟨⟨z,φ,hz,fun _=>rfl,AlgHom.comp_id φ,hφ,H,fun k=>Fin.elim0 k⟩⟩,True.intro⟩
  | cons j js ih=>
    obtain ⟨⟨R⟩,HD⟩:=ih (by simp only [List.length_cons] at room;omega)
    let current:=run x frozen double rows g js (by simp only [List.length_cons] at room;omega)
    have HS : p∈slice P (frame frozen double rows js.length) (values p old js):=by
      rw [slice_values frozen double rows p old js]
      exact hp
    have HP' : PrefixFrozen (frame frozen double rows js.length):=HP
    obtain ⟨_,HC,y,ψ,hy,hold,hphysical,hrestrict,hψ,hvalues⟩:=
      (HP').real_extend_original_point current (by simp only [List.length_cons] at room;omega)
        hn charge hdegree hcap frozen double (shiftRows rows js.length) g.val j.val g.property j.property
        R.tuple R.roots R.hom R.generators (values p old js) R.quotients p HS hg
    refine ⟨⟨⟨y,ψ,hy,?_,?_,hψ,hvalues,?_⟩⟩,HD,HC⟩
    · intro i
      exact (hold _).trans (R.old_raw i)
    · change (ψ.comp (scalarLift current _ (command frozen double rows g js.length j))).comp
        (lift x frozen double rows g js _)=φ
      have HR : ψ.comp (scalarLift current _ (command frozen double rows g js.length j))=R.hom:=hrestrict
      exact (congrArg (fun χ=>χ.comp (lift x frozen double rows g js _)) HR).trans R.old_hom
    · intro k
      refine Fin.cases ?_ (fun k=>?_) k
      · intro i
        simpa only [blockColumn,Fin.cases_zero,Fin.val_zero,List.length_cons,Nat.add_sub_cancel_right,
          Nat.sub_zero] using hphysical i
      · intro i
        have HH:=(hold (blockColumn frozen double rows g js k i)).trans rfl
        change y (Sum.inl (Sum.inl (blockColumn frozen double rows g js k i)))=R.tuple _ at HH
        rw [show blockColumn frozen double rows g (j::js) k.succ i=
          Sum.inl (Sum.inl (blockColumn frozen double rows g js k i)) from rfl,HH]
        have HE : (j::js).length-1-k.succ.val=js.length-1-k.val:=by
          have :=k.isLt
          simp only [List.length_cons,Fin.val_succ]
          omega
        rw [HE]
        exact R.blocks k i

end LeanCanny.Geometry.IntegralMixedPointCompanion
