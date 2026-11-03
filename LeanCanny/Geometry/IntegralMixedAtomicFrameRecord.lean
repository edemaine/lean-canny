/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedOriginalFrameRecord
public import LeanCanny.Geometry.IntegralMixedFrozenFrameNormal
/-! # The actual descending-cover frame grammar stays atomic

The constructed recursive cover starts with zero heights and scale1. Its
recursive calls use advance F h; its temporary sweep uses line F h. Both
preserve this invariant, so they never need nested level sums or an alias
birth. The original point-rule encoder therefore applies to every such frame.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure AtomicRows {n : ℕ} (F : Frame n) (birth : ℕ) : Prop where
  scale : ∀i,F.scales i=1
  row : ∀i,∃a : Atom birth,F.heights i=a.value

noncomputable def AtomicRows.atom {n birth : ℕ} {F : Frame n} (H : AtomicRows F birth)
    (i : Fin (n+1)) : Atom birth:=Classical.choose (H.row i)

theorem AtomicRows.atom_value {n birth : ℕ} {F : Frame n} (H : AtomicRows F birth) (i : Fin (n+1)) :
    F.heights i=(H.atom i).value:=Classical.choose_spec (H.row i)

theorem AtomicRows.initial (n birth : ℕ) : AtomicRows
    ({ frozen:=∅,scales:=fun _=>1,scales_ne_zero:=fun _=>one_ne_zero,heights:=fun _=>.constant 0 } : Frame n) birth:=
  ⟨fun _=>rfl,fun _=>⟨none,rfl⟩⟩

theorem AtomicRows.advance {n birth : ℕ} {F : Frame n} (H : AtomicRows F birth) (h : Fin (n+1)) :
    AtomicRows (advance F h) (birth+1):=by
  constructor
  · intro i
    change (if i=h then 1 else F.scales i)=1
    split_ifs
    · rfl
    · exact H.scale i
  · intro i
    by_cases hi : i=h
    · refine ⟨some 0,?_⟩
      simp only [IntegralMixedFrozenFrame.advance,hi,ite_true,Atom.value]
      rfl
    · obtain ⟨a,ha⟩:=H.row i
      refine ⟨laterAtom a,?_⟩
      simp only [IntegralMixedFrozenFrame.advance,hi,ite_false]
      exact (congrArg later ha).trans (laterAtom_value a).symm

theorem AtomicRows.line {n birth : ℕ} {F : Frame n} (H : AtomicRows F birth) (h : Fin (n+1)) :
    AtomicRows (line F h) birth:=⟨H.scale,H.row⟩

theorem AtomicRows.coarse {n birth : ℕ} {F : Frame n} (H : AtomicRows F birth) (h : Fin (n+1)) :
    AtomicRows (coarse F h) birth:=⟨H.scale,H.row⟩

theorem AtomicRows.frame_eq {n birth : ℕ} {F : Frame n} (H : AtomicRows F birth) :
    F=originalFrame F.frozen (fun _=>false) (fun i=>Row.single (H.atom i)):=by
  cases F with
  | mk frozen scales hscales heights=>
    unfold originalFrame
    congr 1
    · funext i
      exact H.scale i
    · funext i
      exact H.atom_value i

noncomputable def AtomicRows.pointData {n birth : ℕ} {F : Frame n} (H : AtomicRows F birth)
    (g j : Fin (n+1)) (hg : g∉F.frozen) (hj : j∉F.frozen) :
    IntegralMixedCriticalRecordConstructor.Data n birth:=
  originalPointData F.frozen (fun _=>false) (fun i=>Row.single (H.atom i)) g j hg hj

private theorem pointRule_congr {n : ℕ} (F G : Frame n) (g j : Fin (n+1))
    (hg : g∉F.frozen) (hj : j∉F.frozen) (hg' : g∉G.frozen) (hj' : j∉G.frozen) (he : F=G) :
    pointRule F g hg j hj=pointRule G g hg' j hj':=by
  cases he
  rfl

theorem AtomicRows.pointData_rule {n birth : ℕ} {F : Frame n} (H : AtomicRows F birth)
    (g j : Fin (n+1)) (hg : g∉F.frozen) (hj : j∉F.frozen) :
    (H.pointData g j hg hj).rule=pointRule F g hg j hj:=
  (originalPointData_rule F.frozen (fun _=>false) (fun i=>Row.single (H.atom i)) g j hg hj).trans
    (pointRule_congr (originalFrame F.frozen (fun _=>false) (fun i=>Row.single (H.atom i))) F g j hg hj hg hj H.frame_eq.symm)

theorem AtomicRows.pointData_decode {n birth : ℕ} {F : Frame n} (H : AtomicRows F birth)
    (g j : Fin (n+1)) (hg : g∉F.frozen) (hj : j∉F.frozen) :
    IntegralMixedCausalUnitRecordBits.physical n birth (H.pointData g j hg hj).code=pointRule F g hg j hj:=
  (IntegralMixedCriticalRecordConstructor.rule_decode _).trans (H.pointData_rule g j hg hj)

end LeanCanny.Geometry.IntegralMixedFrozenFrame
