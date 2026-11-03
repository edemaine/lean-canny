/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedPrefixOriginalPointRealization
/-! # A literal scale2/refsum midpoint over two jointly retained endpoints

The bank before the anchor is newest-first [b,a,old]. There is no new
midpoint scalar alias: the physical frozen equation is exactly 2*y_h=a+b.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ} {F : Frame n}

noncomputable def midpointRows (H : AtomicRows F m) (h : Fin (n+1))
    (i : Fin (n+1)) : Row (m+2) :=
  if i=h then .sum (some ⟨0,by omega⟩) (some ⟨1,by omega⟩)
    else .single (laterAtom (laterAtom (H.atom i)))

def midpointDouble (h i : Fin (n+1)) : Bool:=decide (i=h)

noncomputable def midpointFrame (H : AtomicRows F m) (h : Fin (n+1)) : Frame n :=
  originalFrame (insert h F.frozen) (midpointDouble h) (midpointRows H h)

theorem midpointFrame_scale (H : AtomicRows F m) (h i : Fin (n+1)) :
    (midpointFrame H h).scales i=if i=h then 2 else 1:=by
  simp only [midpointFrame,originalFrame,midpointDouble,decide_eq_true_eq]

theorem midpointFrame_height (H : AtomicRows F m) (h : Fin (n+1)) :
    (midpointFrame H h).heights h=.add (.reference 0) (.reference 1):=by
  simp only [midpointFrame,originalFrame,midpointRows,ite_true,Row.value,Atom.value]

theorem midpointFrame_old_height (H : AtomicRows F m) (h i : Fin (n+1)) (hi : i≠h) :
    (midpointFrame H h).heights i=later (later (F.heights i)):=by
  simp only [midpointFrame,originalFrame,midpointRows,ite_eq_right hi,Row.value,laterAtom_value]
  rw [H.atom_value]

theorem midpointFrame_slice {P : SpatialSource n} (H : AtomicRows F m) (h : Fin (n+1))
    (hh : h∉F.frozen) (values : Fin m→ℝ) (a b : ℝ) :
    slice P (midpointFrame H h) (Fin.cons b (Fin.cons a values))=
      slice P F values∩{y | y h=(a+b)/2} :=by
  have HE (i : Fin (n+1)) (hi : i≠h) :
      ((midpointFrame H h).heights i).evaluate (Fin.cons b (Fin.cons a values))=
        (F.heights i).evaluate values:=by
    rw [midpointFrame_old_height H h i hi,evaluate_later,evaluate_later]
  ext y
  constructor
  · intro hy
    have HM:=hy.2 h (Finset.mem_insert_self h F.frozen)
    rw [midpointFrame_scale,ite_eq_left rfl,midpointFrame_height] at HM
    change (2 : ℝ)*y h=b+a at HM
    refine ⟨⟨hy.1,?_⟩,?_⟩
    swap
    · change y h=(a+b)/2
      linarith
    intro i hi
    have Hih : i≠h:=fun he=>hh (he ▸ hi)
    have HC:=hy.2 i (Finset.mem_insert_of_mem hi)
    rw [midpointFrame_scale,ite_eq_right Hih,HE i Hih] at HC
    simpa only [H.scale i] using HC
  · rintro ⟨hy,hm⟩
    refine ⟨hy.1,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · rw [midpointFrame_scale,ite_eq_left rfl,midpointFrame_height]
      change (2 : ℝ)*y i=b+a
      change y i=(a+b)/2 at hm
      linarith
    · have Hih : i≠h:=fun he=>hh (he ▸ hi)
      rw [midpointFrame_scale,ite_eq_right Hih,HE i Hih]
      simpa only [H.scale i] using hy.2 i hi

theorem PrefixFrozen.midpointFrame (HP : PrefixFrozen F) (H : AtomicRows F m)
    (h : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen) :
    PrefixFrozen (midpointFrame H h):=by
  have HC : F.frozen.card<n+1:=hfirst ▸ h.isLt
  have HE : h=firstFree F HC:=Fin.ext hfirst
  subst h
  exact HP.advance_first HC

end LeanCanny.Geometry.IntegralMixedFrozenFrame
