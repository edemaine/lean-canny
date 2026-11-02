/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameCut
public import LeanCanny.Algebra.IntegralMixedCriticalSweep

/-! # Current-bank-Q slope gives the literal next affine sweep parameter

Frozen-first ordering changes only spatial names. Choosing the slope from
THIS bank, rather than an earlier initial bank, makes the actual cleared
critical equations exactly the old coarse slice at affine projection t.
The native reader for that current-Q slope remains a separate cost binding.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def critical (F : Frame n) (g : Fin (n+1)) (hg : g∉F.frozen) : CriticalRule n where
  offset := ⟨F.frozen.card,FrozenCoordinateOrdering.card_lt F.frozen g hg⟩
  objective := ((FrozenCoordinateOrdering.permutation F.frozen).symm g).val-F.frozen.card
  coordinate := 0
  scales i := F.scales (FrozenCoordinateOrdering.permutation F.frozen i)
  scales_ne_zero _i := F.scales_ne_zero _
  heights i := F.heights (FrozenCoordinateOrdering.permutation F.frozen i)

noncomputable def sweep (x : State P S B m ι) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (g : Fin (n+1)) (hg : g∉F.frozen) : Rule n where
  critical := critical F g hg
  height := (FrozenCoordinateOrdering.permutation F.frozen).symm h
  height_frozen := (FrozenCoordinateOrdering.inverse_mem_iff F.frozen h).mpr hh
  slope := commonDenominator x
  slope_ne_zero := commonDenominator_ne_zero x

noncomputable def shiftedSlice {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (t : ℝ) : Set (Fin (n+1)→ℝ) :=
  {y | (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y=0 ∧
    ∀ i∈F.frozen,(F.scales i:ℝ)*y i=(F.heights i).evaluate values+if i=h then t else 0}

theorem shiftedSlice_fiber {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (hh : h∈F.frozen) (t : ℝ) :
    shiftedSlice P F values h t=slice P (coarse F h) values∩{y | projection F values h y=t} := by
  ext y
  constructor
  · intro H
    refine ⟨⟨H.1,fun i hi=>?_⟩,?_⟩
    · have HI:=Finset.mem_erase.mp hi
      simpa only [coarse,ite_eq_right HI.1,add_zero] using H.2 i HI.2
    · have HH:=H.2 h hh
      rw [ite_eq_left (rfl : h=h)] at HH
      change (F.scales h:ℝ)*y h-(F.heights h).evaluate values=t
      linarith
  · rintro ⟨H,Ht⟩
    refine ⟨H.1,fun i hi=>?_⟩
    by_cases he : i=h
    · subst i
      rw [ite_eq_left (rfl : h=h)]
      change (F.scales h:ℝ)*y h-(F.heights h).evaluate values=t at Ht
      linarith
    · have HI : i∈(coarse F h).frozen := Finset.mem_erase.mpr ⟨he,hi⟩
      simpa only [coarse,ite_eq_right he,add_zero] using H.2 i HI

theorem sweep_constraint {P : SpatialSource n} (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (g : Fin (n+1)) (hg : g∉F.frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (z : Fin (n+1)→ℝ) (t : ℝ) (i : Fin (n+1)) :
    let e:=FrozenCoordinateOrdering.permutation F.frozen
    let x':=IntegralMixedCoordinateRename.state x e
    ((data x' hm (critical F g hg)).scales i:ℝ)*z i=heightValue x' (sweep x F h hh g hg) φ t i ↔
      (F.scales (e i):ℝ)*z i=(F.heights (e i)).evaluate values+if e i=h then t else 0 := by
  dsimp only
  let e:=FrozenCoordinateOrdering.permutation F.frozen
  have HE : φ (expression (IntegralMixedCoordinateRename.state x e) (F.heights (e i)))=
      (commonDenominator x:ℝ)*(F.heights (e i)).evaluate values :=
    expression_recover (IntegralMixedCoordinateRename.state x e) φ values H _
  change ((commonDenominator x*F.scales (e i):ℤ):ℝ)*z i=
    φ (expression (IntegralMixedCoordinateRename.state x e) (F.heights (e i)))+
      (if i=e.symm h then (commonDenominator x:ℝ)*t else 0) ↔ _
  rw [HE,Int.cast_mul,mul_assoc]
  have HI : i=e.symm h↔e i=h := e.eq_symm_apply
  have HH : (if i=e.symm h then (commonDenominator x:ℝ)*t else 0)=
      (commonDenominator x:ℝ)*(if e i=h then t else 0) := by
    by_cases hj : e i=h
    · rw [ite_eq_left (HI.mpr hj),ite_eq_left hj]
    · rw [ite_eq_right (not_congr HI|>.mpr hj),ite_eq_right hj,mul_zero]
  rw [HH,←mul_add]
  exact ⟨mul_left_cancel₀ (Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)),congrArg ((commonDenominator x:ℝ)*·)⟩

/-- The literal physical slice used by the reordered mixed critical sweep. -/
noncomputable def sweepSlice (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (g : Fin (n+1)) (hg : g∉F.frozen) (t : ℝ) : Set (Fin (n+1)→ℝ) :=
  let e:=FrozenCoordinateOrdering.permutation F.frozen
  let x':=IntegralMixedCoordinateRename.state x e
  {z | (FermatCriticalHomogenization.polynomial
      (IntegralMixedCoordinateRename.spatial P e).low P.leading P.degree).eval₂ (Int.castRingHom ℝ) z=0 ∧
    ∀ i, i.val<F.frozen.card→
      ((data x' hm (critical F g hg)).scales i:ℝ)*z i=heightValue x' (sweep x F h hh g hg) φ t i}

theorem sweepSlice_eq (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (g : Fin (n+1)) (hg : g∉F.frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i) (t : ℝ) :
    sweepSlice x hm φ F h hh g hg t=
      {z | z ∘ (FrozenCoordinateOrdering.permutation F.frozen).symm∈
        slice P (coarse F h) values∩{y | projection F values h y=t}} := by
  rw [←shiftedSlice_fiber P F values h hh t]
  let e:=FrozenCoordinateOrdering.permutation F.frozen
  ext z
  constructor
  · intro hz
    refine ⟨(IntegralMixedCoordinateRename.source_eval P e z).symm.trans hz.1,?_⟩
    intro j hj
    have HI : (e.symm j).val<F.frozen.card:=
      (FrozenCoordinateOrdering.inverse_mem_iff F.frozen j).mpr hj
    have HC:=(sweep_constraint x hm φ F h hh g hg values H z t (e.symm j)).mp (hz.2 _ HI)
    simpa only [e,Equiv.apply_symm_apply,Function.comp_apply] using HC
  · intro hz
    refine ⟨(IntegralMixedCoordinateRename.source_eval P e z).trans hz.1,?_⟩
    intro i hi
    have HI : e i∈F.frozen:= (FrozenCoordinateOrdering.permutation_mem_iff F.frozen i).mpr hi
    apply (sweep_constraint x hm φ F h hh g hg values H z t i).mpr
    simpa only [e,Function.comp_apply,Equiv.symm_apply_apply] using hz.2 (e i) HI

end LeanCanny.Geometry.IntegralMixedFrozenFrame
