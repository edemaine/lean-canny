/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalFrameRetained
public import LeanCanny.Geometry.IntegralMixedReferencedMidpointFrame
/-! # A chronological descriptor's literal scale-two midpoint frame -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalMidpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth : ℕ}

def reference (a : Fin birth) : Fin birth:=⟨birth-1-a.val,by have :=a.isLt;omega⟩
def next (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1) : Fin (n+1):=
  ⟨d.labels.length,hk⟩

def rows (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (i : Fin (n+1)) : Row birth:=
  if i=next d hk then .sum (some (reference a)) (some (reference b)) else .single (d.atom i)

noncomputable def frame (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) : Frame n:=
  originalFrame (insert (next d hk) d.frame.frozen) (midpointDouble (next d hk)) (rows d hk a b)

theorem next_not_mem (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1) :
    next d hk∉d.frame.frozen :=by
  rw [d.frozen_mem]
  exact Nat.lt_irrefl _

theorem frame_eq (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) :
    frame d hk a b=referencedMidpointFrame d.atomic (next d hk) (reference a) (reference b) :=by
  unfold frame referencedMidpointFrame originalFrame
  congr 1
  funext i
  by_cases hi : i=next d hk
  · simp only [rows,referencedMidpointRows,ite_eq_left hi]
  · simp only [rows,referencedMidpointRows,ite_eq_right hi,Row.value]
    exact d.atomic.atom_value i

theorem frozen_mem (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (i : Fin (n+1)) :
    i∈(frame d hk a b).frozen ↔ i.val<d.labels.length+1 :=by
  change i∈insert (next d hk) d.frame.frozen↔_
  rw [Finset.mem_insert,d.frozen_mem,Fin.ext_iff]
  dsimp only [next]
  omega

theorem frozen_card (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) : (frame d hk a b).frozen.card=d.labels.length+1 :=by
  change (insert (next d hk) d.frame.frozen).card=_
  rw [Finset.card_insert_of_notMem (next_not_mem d hk),d.frozen_card]

theorem prefix_frozen (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) : PrefixFrozen (frame d hk a b) :=by
  intro i
  rw [frozen_mem,frozen_card]

theorem free_iff (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (i : Fin (n+1)) :
    i∉(frame d hk a b).frozen ↔ d.labels.length+1≤ i.val :=by
  rw [frozen_mem,Nat.not_lt]

theorem free_normal (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) : FreeNormal (frame d hk a b) :=by
  intro i hi
  have HO : i∉d.frame.frozen:=by
    intro h
    exact hi (Finset.mem_insert_of_mem h)
  have HN : i≠next d hk:=by
    intro he
    subst i
    exact hi (Finset.mem_insert_self _ _)
  rw [frame_eq,referencedMidpointFrame_scale,ite_eq_right HN,
    referencedMidpointFrame_old_height d.atomic (next d hk) (reference a) (reference b) i HN]
  exact d.free_normal i HO

theorem slice_eq (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (P : SpatialSource n) (values : Fin birth→ℝ) :
    slice P (frame d hk a b) values=
      slice P d.frame values∩{p | p (next d hk)=(values (reference a)+values (reference b))/2} :=by
  rw [frame_eq]
  exact referencedMidpointFrame_slice d.atomic (next d hk) (next_not_mem d hk) _ _ values

theorem reference_word (a : Fin birth) :
    Atom.word (some (reference a) : Atom birth)=pair [true] (BinaryNatCode.encode a.val) :=by
  have HR : birth-1-a.val<birth:=(reference a).isLt
  have HE : birth-1-(birth-1-a.val)=a.val:=by have :=a.isLt;omega
  simp only [Atom.word,reference,referenceWord,HR,decide_true,HE]

end LeanCanny.Geometry.IntegralMixedChronologicalMidpoint
