/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalMidpointSignature
/-! # Actual hom readback and same-slab identity for midpoint signatures -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalMidpointSignature
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedPointCompanion IntegralMixedFullHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B birth : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

 theorem realized_signature_value (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth) (x : State P S B birth ι)
    (g : Free (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (z : ι→ℝ) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (old : Fin birth→ℝ)
    (p : Fin (n+1)→ℝ) (hp : p∈slice P (IntegralMixedChronologicalMidpoint.frame d hk a b) old)
    (room : birth+(orderedFree d hk a b).length≤S+1)
    (R : Realized x (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen
      (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk)) (IntegralMixedChronologicalMidpoint.rows d hk a b)
      g z φ old p (orderedFree d hk a b) room) (i : Fin (n+1)) :
    let result:=run x (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen
      (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk)) (IntegralMixedChronologicalMidpoint.rows d hk a b)
      g (orderedFree d hk a b) room
    let final : Fin (birth+freeCount d)→ℝ:=fun j=>R.hom (result.bank.numerator
      ⟨j.val,by rw [orderedFree_length];exact j.isLt⟩)/(result.bank.denominator
      ⟨j.val,by rw [orderedFree_length];exact j.isLt⟩:ℝ)
    Feature.eval final (signature d a b i)=p i :=by
  dsimp only
  have HE : (fun j : Fin (birth+freeCount d)=>R.hom ((run x
      (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen
      (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk)) (IntegralMixedChronologicalMidpoint.rows d hk a b)
      g (orderedFree d hk a b) room).bank.numerator ⟨j.val,by rw [orderedFree_length];exact j.isLt⟩)/
      ((run x (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen
      (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk)) (IntegralMixedChronologicalMidpoint.rows d hk a b)
      g (orderedFree d hk a b) room).bank.denominator ⟨j.val,by rw [orderedFree_length];exact j.isLt⟩:ℝ))=
      postValues d hk a b p old:=by
    funext j
    exact R.quotients _
  rw [HE]
  exact point_values d hk a b P old p hp i

omit [Fintype ι] in
theorem same_slab_point_eq {otherBirth : ℕ}
    (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (e : IntegralMixedChronologicalFrame.Descriptor n otherBirth)
    (hk : d.labels.length<n+1) (he : e.labels.length<n+1) (hlen : d.labels.length=e.labels.length)
    (a b : Fin birth) (c f : Fin otherBirth) (old : Fin birth→ℝ) (other : Fin otherBirth→ℝ)
    (p q : Fin (n+1)→ℝ)
    (hp : p∈slice P (IntegralMixedChronologicalMidpoint.frame d hk a b) old)
    (hq : q∈slice P (IntegralMixedChronologicalMidpoint.frame e he c f) other)
    (Hlevels : ∀i : Fin d.labels.length,old (d.reference i)=other (e.reference (Fin.cast hlen i)))
    (Ha : old (IntegralMixedChronologicalMidpoint.reference a)=other (IntegralMixedChronologicalMidpoint.reference c))
    (Hb : old (IntegralMixedChronologicalMidpoint.reference b)=other (IntegralMixedChronologicalMidpoint.reference f))
    (Hfree : ∀i : Fin (n+1),d.labels.length+1≤ i.val→
      Feature.eval (postValues d hk a b p old) (signature d a b i)=
      Feature.eval (postValues e he c f q other) (signature e c f i)) : p=q :=by
  have HD:=hp
  have HE:=hq
  rw [IntegralMixedChronologicalMidpoint.slice_eq] at HD HE
  funext i
  by_cases hi : i.val<d.labels.length
  · have HP:=((d.slice_iff P old p).mp HD.1).2 ⟨i.val,hi⟩
    have HQ:=((e.slice_iff P other q).mp HE.1).2 (Fin.cast hlen ⟨i.val,hi⟩)
    exact HP.trans ((Hlevels ⟨i.val,hi⟩).trans HQ.symm)
  · by_cases hm : i.val=d.labels.length
    · have HI : i=IntegralMixedChronologicalMidpoint.next d hk:=Fin.ext hm
      have HJ : i=IntegralMixedChronologicalMidpoint.next e he:=Fin.ext (hm.trans hlen)
      calc
        p i=p (IntegralMixedChronologicalMidpoint.next d hk):=congrArg p HI
        _=(old (IntegralMixedChronologicalMidpoint.reference a)+old (IntegralMixedChronologicalMidpoint.reference b))/2:=HD.2
        _=(other (IntegralMixedChronologicalMidpoint.reference c)+other (IntegralMixedChronologicalMidpoint.reference f))/2:=by rw [Ha,Hb]
        _=q (IntegralMixedChronologicalMidpoint.next e he):=HE.2.symm
        _=q i:=congrArg q HJ.symm
    · exact (point_values d hk a b P old p hp i).symm.trans
        ((Hfree i (by omega)).trans (point_values e he c f P other q hq i))

end LeanCanny.Geometry.IntegralMixedChronologicalMidpointSignature
