/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FrozenCoordinatePrefixOrdering
public import LeanCanny.Geometry.IntegralMixedAtomicFrameRecord
/-! # Deterministic first-free frames keep the original spatial source

The descending cover permits any free h and, when two remain, a free g in
line F h. The explicit choices below are offset and offset+1. Both recursive
advance and temporary line retain an initial frozen segment, so the existing
frozen-first permutation is identity and source coefficients are unchanged.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def PrefixFrozen (F : Frame n) : Prop:=∀i,i∈F.frozen↔i.val<F.frozen.card

theorem PrefixFrozen.of_empty (F : Frame n) (he : F.frozen=∅) : PrefixFrozen F:=by
  intro i
  simp only [he,Finset.notMem_empty,Finset.card_empty,Nat.not_lt_zero]

def firstFree (F : Frame n) (h : F.frozen.card<n+1) : Fin (n+1):=⟨F.frozen.card,h⟩

theorem PrefixFrozen.firstFree_notMem {F : Frame n} (H : PrefixFrozen F) (h : F.frozen.card<n+1) :
    firstFree F h∉F.frozen:=by
  intro hi
  exact (Nat.lt_irrefl F.frozen.card) ((H _).mp hi)

def secondFree (F : Frame n) (h : F.frozen.card+1<n+1) : Fin (n+1):=⟨F.frozen.card+1,h⟩

theorem PrefixFrozen.secondFree_not_line {F : Frame n} (H : PrefixFrozen F)
    (h : F.frozen.card+1<n+1) : secondFree F h∉(line F (firstFree F (by omega))).frozen:=by
  intro hi
  rcases Finset.mem_insert.mp hi with he|he
  · have HV:=congrArg Fin.val he
    change F.frozen.card+1=F.frozen.card at HV
    omega
  · have HV:=(H _).mp he
    change F.frozen.card+1<F.frozen.card at HV
    omega

theorem PrefixFrozen.advance_first {F : Frame n} (H : PrefixFrozen F) (h : F.frozen.card<n+1) :
    PrefixFrozen (advance F (firstFree F h)):=by
  intro i
  simp only [advance,Finset.mem_insert,Finset.card_insert_of_notMem (H.firstFree_notMem h)]
  rw [H i]
  simp only [firstFree,Fin.ext_iff]
  omega

theorem PrefixFrozen.line_first {F : Frame n} (H : PrefixFrozen F) (h : F.frozen.card<n+1) :
    PrefixFrozen (line F (firstFree F h)):=H.advance_first h

theorem AtomicRows.retained {F : Frame n} {birth : ℕ} (H : AtomicRows F birth) :
    AtomicRows (retained F) (birth+1):=by
  constructor
  · exact H.scale
  · intro i
    refine ⟨laterAtom (H.atom i),?_⟩
    exact (congrArg later (H.atom_value i)).trans (laterAtom_value _).symm

theorem PrefixFrozen.retained {F : Frame n} (H : PrefixFrozen F) : PrefixFrozen (retained F):=H

theorem FreeNormal.retained {F : Frame n} (H : FreeNormal F) : FreeNormal (retained F):=by
  intro i hi
  obtain ⟨hs,hh⟩:=H i hi
  exact ⟨hs,congrArg later hh⟩

theorem PrefixFrozen.permutation {F : Frame n} (H : PrefixFrozen F) :
    FrozenCoordinateOrdering.permutation F.frozen=Equiv.refl (Fin (n+1)):=
  FrozenCoordinateOrdering.permutation_eq_refl F.frozen H

theorem PrefixFrozen.spatial {F : Frame n} (H : PrefixFrozen F) (P : SpatialSource n) :
    IntegralMixedCoordinateRename.spatial P (FrozenCoordinateOrdering.permutation F.frozen)=P:=by
  rw [H.permutation]
  cases P
  simp only [IntegralMixedCoordinateRename.spatial,show ((Equiv.refl (Fin (n+1))).symm : Fin (n+1)→Fin (n+1))=id from rfl,
    MvPolynomial.rename_id_apply]

private theorem reframe_heq {S B m : ℕ} {P Q : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hc : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B) (he : Q=P) :
    HEq (reframe x Q hc) x:=by
  cases he
  cases x
  rfl

theorem PrefixFrozen.state_heq {F : Frame n} (H : PrefixFrozen F) {S B m : ℕ} {P : SpatialSource n}
    {ι : Type} (x : State P S B m ι) :
    HEq (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) x:=
  reframe_heq (Q:=IntegralMixedCoordinateRename.spatial P (FrozenCoordinateOrdering.permutation F.frozen))
    x x.critical_cap (H.spatial P)

private theorem critical_heq {S B m : ℕ} {P Q : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (y : State Q S B m ι) (he : Q=P) (hxy : HEq y x)
    (hm : m≤S) (r : CriticalRule n) : HEq (criticalStep y hm r) (criticalStep x hm r):=by
  cases he
  have h:=eq_of_heq hxy
  cases h
  rfl

theorem PrefixFrozen.criticalStep_heq {F : Frame n} (H : PrefixFrozen F) {S B m : ℕ} {P : SpatialSource n}
    {ι : Type} [Fintype ι] (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n) :
    HEq (criticalStep (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm r)
      (criticalStep x hm r):=
  critical_heq (Q:=IntegralMixedCoordinateRename.spatial P (FrozenCoordinateOrdering.permutation F.frozen))
    x (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen))
    (H.spatial P) (H.state_heq x) hm r

/-- These are exactly the free-slot hypotheses used by the nonterminal
recursive cover step; the choices are determined by the frozen offset. -/
theorem PrefixFrozen.exists_step {F : Frame n} (H : PrefixFrozen F) (hk : 1<n+1-F.frozen.card) :
    ∃h g : Fin (n+1),h.val=F.frozen.card ∧ g.val=F.frozen.card+1 ∧
      h∉F.frozen ∧ g∉(line F h).frozen ∧ PrefixFrozen (advance F h) ∧ PrefixFrozen (line F h):=by
  have H1 : F.frozen.card<n+1:=by omega
  have H2 : F.frozen.card+1<n+1:=by omega
  exact ⟨firstFree F H1,secondFree F H2,rfl,rfl,H.firstFree_notMem H1,
    H.secondFree_not_line H2,H.advance_first H1,H.line_first H1⟩

end LeanCanny.Geometry.IntegralMixedFrozenFrame
