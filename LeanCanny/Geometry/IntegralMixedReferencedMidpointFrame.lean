/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedJointMidpointFrame
/-! # Literal frozen frames referencing arbitrary retained endpoint labels -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ} {F : Frame n}

noncomputable def referencedMidpointRows (HA : AtomicRows F m) (h : Fin (n+1)) (u v : Fin m)
    (i : Fin (n+1)) : Row m:=
  if i=h then .sum (some u) (some v) else .single (HA.atom i)

noncomputable def referencedMidpointFrame (HA : AtomicRows F m) (h : Fin (n+1)) (u v : Fin m) : Frame n:=
  originalFrame (insert h F.frozen) (midpointDouble h) (referencedMidpointRows HA h u v)

theorem referencedMidpointFrame_scale (HA : AtomicRows F m) (h : Fin (n+1)) (u v : Fin m) (i : Fin (n+1)) :
    (referencedMidpointFrame HA h u v).scales i=if i=h then 2 else 1:=by
  simp only [referencedMidpointFrame,originalFrame,midpointDouble,decide_eq_true_eq]

theorem referencedMidpointFrame_height (HA : AtomicRows F m) (h : Fin (n+1)) (u v : Fin m) :
    (referencedMidpointFrame HA h u v).heights h=.add (.reference u.val) (.reference v.val):=by
  simp only [referencedMidpointFrame,originalFrame,referencedMidpointRows,ite_true,Row.value,Atom.value]

theorem referencedMidpointFrame_old_height (HA : AtomicRows F m) (h : Fin (n+1)) (u v : Fin m)
    (i : Fin (n+1)) (hi : i≠h) : (referencedMidpointFrame HA h u v).heights i=F.heights i:=by
  simp only [referencedMidpointFrame,originalFrame,referencedMidpointRows,ite_eq_right hi,Row.value]
  exact (HA.atom_value i).symm

theorem referencedMidpointFrame_slice {P : SpatialSource n} (HA : AtomicRows F m)
    (h : Fin (n+1)) (hh : h∉F.frozen) (u v : Fin m) (values : Fin m→ℝ) :
    slice P (referencedMidpointFrame HA h u v) values=
      slice P F values∩{y | y h=(values u+values v)/2} :=by
  have HR (i : Fin m) : (AffineExpr.reference i.val).evaluate values=values i:=by
    simp only [AffineExpr.evaluate,dite_eq_left i.isLt]
  ext y
  constructor
  · intro hy
    have HM:=hy.2 h (Finset.mem_insert_self h F.frozen)
    rw [referencedMidpointFrame_scale,ite_eq_left rfl,referencedMidpointFrame_height] at HM
    change (2:ℝ)*y h=(AffineExpr.reference u.val).evaluate values+(AffineExpr.reference v.val).evaluate values at HM
    rw [HR,HR] at HM
    refine ⟨⟨hy.1,?_⟩,?_⟩
    swap
    · change y h=(values u+values v)/2
      linarith
    intro i hi
    have Hih : i≠h:=fun he=>hh (he ▸ hi)
    have HC:=hy.2 i (Finset.mem_insert_of_mem hi)
    rw [referencedMidpointFrame_scale,ite_eq_right Hih,referencedMidpointFrame_old_height HA h u v i Hih] at HC
    simpa only [HA.scale i,Int.cast_one] using HC
  · rintro ⟨hy,hm⟩
    refine ⟨hy.1,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with HE|hi
    · subst i
      rw [referencedMidpointFrame_scale,ite_eq_left rfl,referencedMidpointFrame_height]
      change (2:ℝ)*y h=(AffineExpr.reference u.val).evaluate values+(AffineExpr.reference v.val).evaluate values
      rw [HR,HR]
      change y h=(values u+values v)/2 at hm
      linarith
    · have Hih : i≠h:=fun he=>hh (he ▸ hi)
      rw [referencedMidpointFrame_scale,ite_eq_right Hih,referencedMidpointFrame_old_height HA h u v i Hih]
      simpa only [HA.scale i,Int.cast_one] using hy.2 i hi

theorem PrefixFrozen.referencedMidpointFrame (HP : PrefixFrozen F) (HA : AtomicRows F m)
    (h : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen) (u v : Fin m) :
    PrefixFrozen (referencedMidpointFrame HA h u v):=by
  have HC : F.frozen.card<n+1:=hfirst ▸ h.isLt
  have HE : h=firstFree F HC:=Fin.ext hfirst
  subst h
  exact HP.advance_first HC

noncomputable def referencedEndpointRows (HA : AtomicRows F m) (h : Fin (n+1)) (u : Fin m)
    (i : Fin (n+1)) : Row m:=if i=h then .single (some u) else .single (HA.atom i)

noncomputable def referencedEndpointFrame (HA : AtomicRows F m) (h : Fin (n+1)) (u : Fin m) : Frame n:=
  originalFrame (insert h F.frozen) (fun _=>false) (referencedEndpointRows HA h u)

theorem referencedEndpointFrame_scale (HA : AtomicRows F m) (h : Fin (n+1)) (u : Fin m) (i : Fin (n+1)) :
    (referencedEndpointFrame HA h u).scales i=1:=rfl

theorem referencedEndpointFrame_height (HA : AtomicRows F m) (h : Fin (n+1)) (u : Fin m) :
    (referencedEndpointFrame HA h u).heights h=.reference u.val:=by
  simp only [referencedEndpointFrame,originalFrame,referencedEndpointRows,ite_true,Row.value,Atom.value]

theorem referencedEndpointFrame_old_height (HA : AtomicRows F m) (h : Fin (n+1)) (u : Fin m)
    (i : Fin (n+1)) (hi : i≠h) : (referencedEndpointFrame HA h u).heights i=F.heights i:=by
  simp only [referencedEndpointFrame,originalFrame,referencedEndpointRows,ite_eq_right hi,Row.value]
  exact (HA.atom_value i).symm

theorem referencedEndpointFrame_atomic (HA : AtomicRows F m) (h : Fin (n+1)) (u : Fin m) :
    AtomicRows (referencedEndpointFrame HA h u) m:=by
  constructor
  · intro i
    rfl
  · intro i
    by_cases hi : i=h
    · exact ⟨some u,by subst i; exact referencedEndpointFrame_height HA h u⟩
    · exact ⟨HA.atom i,(referencedEndpointFrame_old_height HA h u i hi).trans (HA.atom_value i)⟩

theorem PrefixFrozen.referencedEndpointFrame (HP : PrefixFrozen F) (HA : AtomicRows F m)
    (h : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen) (u : Fin m) :
    PrefixFrozen (referencedEndpointFrame HA h u):=by
  have HC : F.frozen.card<n+1:=hfirst ▸ h.isLt
  have HE : h=firstFree F HC:=Fin.ext hfirst
  subst h
  exact HP.advance_first HC

theorem FreeNormal.referencedEndpointFrame (HF : FreeNormal F) (HA : AtomicRows F m)
    (h : Fin (n+1)) (u : Fin m) : FreeNormal (referencedEndpointFrame HA h u):=by
  intro i hi
  have HI : i≠h ∧ i∉F.frozen:=by
    change i∉insert h F.frozen at hi
    simpa only [Finset.mem_insert,not_or] using hi
  refine ⟨rfl,?_⟩
  rw [referencedEndpointFrame_old_height HA h u i HI.1]
  exact (HF i HI.2).2

theorem referencedEndpointFrame_slice {P : SpatialSource n} (HA : AtomicRows F m)
    (h : Fin (n+1)) (hh : h∉F.frozen) (u : Fin m) (values : Fin m→ℝ) :
    slice P (referencedEndpointFrame HA h u) values=slice P F values∩{y | y h=values u} :=by
  have HR : (AffineExpr.reference u.val).evaluate values=values u:=by
    simp only [AffineExpr.evaluate,dite_eq_left u.isLt]
  ext y
  constructor
  · intro hy
    have HM:=hy.2 h (Finset.mem_insert_self h F.frozen)
    rw [referencedEndpointFrame_height,referencedEndpointFrame_scale,Int.cast_one] at HM
    change (1:ℝ)*y h=(AffineExpr.reference u.val).evaluate values at HM
    rw [HR,one_mul] at HM
    refine ⟨⟨hy.1,?_⟩,HM⟩
    intro i hi
    have HI : i≠h:=fun he=>hh (he ▸ hi)
    have HC:=hy.2 i (Finset.mem_insert_of_mem hi)
    rw [referencedEndpointFrame_old_height HA h u i HI,referencedEndpointFrame_scale,Int.cast_one] at HC
    change (1:ℝ)*y i=(F.heights i).evaluate values at HC
    simpa only [HA.scale i,Int.cast_one] using HC
  · rintro ⟨hy,hu⟩
    refine ⟨hy.1,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with HE|hi
    · subst i
      rw [referencedEndpointFrame_height,referencedEndpointFrame_scale,Int.cast_one]
      change (1:ℝ)*y h=(AffineExpr.reference u.val).evaluate values
      rw [HR,one_mul,hu]
    · have HI : i≠h:=fun he=>hh (he ▸ hi)
      rw [referencedEndpointFrame_old_height HA h u i HI,referencedEndpointFrame_scale,Int.cast_one]
      change (1:ℝ)*y i=(F.heights i).evaluate values
      simpa only [HA.scale i,Int.cast_one] using hy.2 i hi

end LeanCanny.Geometry.IntegralMixedFrozenFrame
