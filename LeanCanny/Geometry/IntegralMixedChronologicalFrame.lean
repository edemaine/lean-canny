/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedPrefixFrame
/-! # Frozen prefix frames addressed by chronological producer labels

The descriptor contains only bounded labels, before any sampler word is
allocated. Its actual retained-bank references use the current birth. Each
label therefore keeps its meaning when later records are retained.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Descriptor (n birth : ℕ) where
  labels : List (Fin birth)
  length_le : labels.length≤n+1

namespace Descriptor
variable {n birth : ℕ}

def reference (d : Descriptor n birth) (i : Fin d.labels.length) : Fin birth :=
  ⟨birth-1-(d.labels[i]).val,by have :=(d.labels[i]).isLt;omega⟩

def atom (d : Descriptor n birth) (i : Fin (n+1)) : Atom birth :=
  if hi : i.val<d.labels.length then some (d.reference ⟨i.val,hi⟩) else none

noncomputable def frame (d : Descriptor n birth) : Frame n :=
  originalFrame (Finset.univ.filter (fun i : Fin (n+1)=>i.val<d.labels.length))
    (fun _=>false) (fun i=>.single (d.atom i))

theorem frozen_mem (d : Descriptor n birth) (i : Fin (n+1)) :
    i∈d.frame.frozen ↔ i.val<d.labels.length :=by
  simp only [frame,originalFrame,Finset.mem_filter,Finset.mem_univ,true_and]

theorem frozen_card (d : Descriptor n birth) : d.frame.frozen.card=d.labels.length :=by
  change (Finset.univ.filter (fun i : Fin (n+1)=>i.val<d.labels.length)).card=_
  rw [Fin.card_filter_val_lt,min_eq_right d.length_le]

theorem prefix_frozen (d : Descriptor n birth) : PrefixFrozen d.frame :=by
  intro i
  rw [d.frozen_mem,d.frozen_card]

theorem atomic (d : Descriptor n birth) : AtomicRows d.frame birth :=
  ⟨fun _=>rfl,fun i=>⟨d.atom i,rfl⟩⟩

theorem free_normal (d : Descriptor n birth) : FreeNormal d.frame :=by
  intro i hi
  have HI : ¬i.val<d.labels.length:=fun h=>hi ((d.frozen_mem i).mpr h)
  exact ⟨rfl,by simp only [frame,originalFrame,Row.value,atom,dite_eq_right HI,Atom.value]⟩

theorem height (d : Descriptor n birth) (i : Fin d.labels.length) :
    d.frame.heights ⟨i.val,lt_of_lt_of_le i.isLt d.length_le⟩=
      .reference (birth-1-(d.labels[i]).val) :=by
  change (d.atom ⟨i.val,_⟩).value=_
  rw [atom,dite_eq_left i.isLt]
  rfl

theorem slice_iff (d : Descriptor n birth) (P : SpatialSource n) (values : Fin birth→ℝ)
    (point : Fin (n+1)→ℝ) :
    point∈slice P d.frame values ↔
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) point=0 ∧
        ∀i : Fin d.labels.length,point ⟨i.val,lt_of_lt_of_le i.isLt d.length_le⟩=values (d.reference i) :=by
  constructor
  · intro H
    refine ⟨H.1,?_⟩
    intro i
    have HI:=H.2 ⟨i.val,lt_of_lt_of_le i.isLt d.length_le⟩ ((d.frozen_mem _).mpr i.isLt)
    rw [d.atomic.scale _,Int.cast_one,one_mul,d.height i] at HI
    change point ⟨i.val,lt_of_lt_of_le i.isLt d.length_le⟩=
      (if h : (d.reference i).val<birth then values ⟨(d.reference i).val,h⟩ else 0) at HI
    rw [dite_eq_left (d.reference i).isLt] at HI
    exact HI
  · rintro ⟨H,Hlevels⟩
    refine ⟨H,?_⟩
    intro i hi
    have HI : i.val<d.labels.length:=(d.frozen_mem i).mp hi
    let j : Fin d.labels.length:=⟨i.val,HI⟩
    have HE : (⟨j.val,lt_of_lt_of_le j.isLt d.length_le⟩ : Fin (n+1))=i:=Fin.ext rfl
    have HH:=d.height j
    rw [HE] at HH
    rw [d.atomic.scale i,Int.cast_one,one_mul,HH]
    change point i=(if h : (d.reference j).val<birth then values ⟨(d.reference j).val,h⟩ else 0)
    rw [dite_eq_left (d.reference j).isLt]
    simpa only [HE] using Hlevels j

end Descriptor
end LeanCanny.Geometry.IntegralMixedChronologicalFrame
