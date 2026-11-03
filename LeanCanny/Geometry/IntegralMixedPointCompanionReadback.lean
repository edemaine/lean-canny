/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedPointCompanionTrace
/-! # Capturing all free coordinates identifies the whole physical point -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedPointCompanion
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedCausalRowConstructor IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

noncomputable def allFree (frozen : Finset (Fin (n+1))) : List (Free frozen):=Finset.univ.toList

theorem mem_allFree (frozen : Finset (Fin (n+1))) (j : Free frozen) : j∈allFree frozen:=by
  simp only [allFree,Finset.mem_toList,Finset.mem_univ]

theorem allFree_length (frozen : Finset (Fin (n+1))) : (allFree frozen).length≤n+1:=by
  have H:=Fintype.card_subtype_le (fun j : Fin (n+1)=>j∉frozen)
  simpa only [allFree,Finset.length_toList,Finset.card_univ,Fintype.card_fin] using H

theorem values_get {frozen : Finset (Fin (n+1))} (p : Fin (n+1)→ℝ) (old : Fin m→ℝ)
    (js : List (Free frozen)) (k : Fin js.length) :
    values p old js ⟨k.val,by have :=k.isLt;omega⟩=p (js.get k).val :=by
  induction js with
  | nil=>exact Fin.elim0 k
  | cons j js ih=>
    refine Fin.cases ?_ (fun k=>?_) k
    · rfl
    · exact ih k

theorem values_old {frozen : Finset (Fin (n+1))} (p : Fin (n+1)→ℝ) (old : Fin m→ℝ)
    (js : List (Free frozen)) (i : Fin m) :
    values p old js ⟨js.length+i.val,by have :=i.isLt;omega⟩=old i :=by
  induction js with
  | nil=>
    apply congrArg old
    apply Fin.ext
    simp only [List.length_nil,Nat.zero_add]
  | cons j js ih=>
    let a : Fin (m+js.length):=⟨js.length+i.val,by have :=i.isLt;omega⟩
    have HE : (⟨(j::js).length+i.val,by have :=i.isLt;omega⟩ : Fin (m+(j::js).length))=a.succ:=by
      apply Fin.ext
      dsimp only [a]
      simp only [List.length_cons,Fin.val_succ]
      omega
    change Fin.cons (α:=fun _ : Fin (m+js.length+1)=>ℝ) (p j.val) (values p old js) _=old i
    rw [HE]
    exact ih

theorem point_eq_of_free {F : Frame n} {old : Fin m→ℝ} {p q : Fin (n+1)→ℝ}
    (hp : p∈slice P F old) (hq : q∈slice P F old)
    (H : ∀j : Free F.frozen,p j.val=q j.val) : p=q :=by
  funext i
  by_cases hi : i∈F.frozen
  · exact mul_left_cancel₀ (Int.cast_ne_zero.mpr (F.scales_ne_zero i))
      ((hp.2 i hi).trans (hq.2 i hi).symm)
  · exact H ⟨i,hi⟩

variable (x : State P S B m ι) (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen)
    (z : ι→ℝ) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (old : Fin m→ℝ) (p : Fin (n+1)→ℝ) (js : List (Free frozen)) (room : m+js.length≤S+1)
    (R : Realized x frozen double rows g z φ old p js room)

theorem Realized.capture (k : Fin js.length) :
    R.hom ((run x frozen double rows g js room).bank.numerator ⟨k.val,by have :=k.isLt;omega⟩)/
      ((run x frozen double rows g js room).bank.denominator ⟨k.val,by have :=k.isLt;omega⟩:ℝ)=
      p (js.get k).val :=(R.quotients _).trans (values_get p old js k)

theorem Realized.old_value (i : Fin m) :
    R.hom ((run x frozen double rows g js room).bank.numerator ⟨js.length+i.val,by have :=i.isLt;omega⟩)/
      ((run x frozen double rows g js room).bank.denominator ⟨js.length+i.val,by have :=i.isLt;omega⟩:ℝ)=old i :=
  (R.quotients _).trans (values_old p old js i)

 theorem exists_all_free (hn : 0<n) (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (HP : PrefixFrozen (originalFrame frozen double rows))
    (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^UniformIntegralPowerSchedule.weights S (2^B) m i)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=old i)
    (hp : p∈slice P (originalFrame frozen double rows) old)
    (hg : ∀i,i∉frozen→i≠g.val→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (hroom : m+n+1≤S+1) :
    ∃room : m+(allFree frozen).length≤S+1,
      Nonempty (Realized x frozen double rows g z φ old p (allFree frozen) room) ∧
      Decoded x frozen double rows g hn hcap (allFree frozen) room :=by
  have HR : m+(allFree frozen).length≤S+1:=by have :=allFree_length frozen;omega
  exact ⟨HR,exists_realized x frozen double rows g hn charge hdegree hcap HP z hz φ hφ old H p hp hg _ HR⟩

end LeanCanny.Geometry.IntegralMixedPointCompanion
