/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedMatchedSlabInterior
public import LeanCanny.Connectivity.AccessibleArc
/-! # An anchored Near certificate gives an actual local path

The section word belongs to the captured physical midpoint. This premise
cannot be replaced by an arbitrary tuple of coordinate branch ordinals.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame.MatchedSlabInterior
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
variable {x : State P S B m ι} {hm : m≤S}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {F : Frame n}
    {h : Fin (n+1)} {hh : h∈F.frozen} {g : Fin (n+1)} {hg : g∉F.frozen}
    {values : Fin m→ℝ} {a b : ℝ} {t₀ : Ioo a b}
    (M : MatchedSlabInterior x hm φ F h hh g hg values a b t₀)

theorem code_anchor
    (i : IntegralMixedSelectedPhysicalFiber.physical
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ t₀.val) :
    M.code i=IntegralMixedFrozenFrameSectionCode.word
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ t₀.val i :=by
  have HE : (⟨M.curve i t₀.val,M.physical i t₀.val (Ioo_subset_Icc_self t₀.property)⟩ :
      IntegralMixedSelectedPhysicalFiber.physical
        (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
        (sweep x F h hh g hg) φ t₀.val)=i:=Subtype.ext (M.anchor i)
  have HW:=M.code_word i t₀
  rw [HE] at HW
  exact HW.symm

include M in
theorem joined_of_near
    (i : IntegralMixedSelectedPhysicalFiber.physical
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ t₀.val)
    (endpoint : ℝ) (he : endpoint∈Icc a b) (y : Fin (n+1)→ℝ)
    (hy : IntegralMixedSelectedCoordinateEndpoint.Frozen
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ endpoint y)
    (code : List Bool)
    (hcode : code=IntegralMixedFrozenFrameSectionCode.word
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ t₀.val i)
    (hnear : ∀j : IntegralMixedSelectedGeometry.Free (sweep x F h hh g hg),
      IntegralMixedSelectedCoordinateEndpoint.Near
        (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
        (sweep x F h hh g hg) φ a b endpoint j
        (IntegralMixedSelectedCoordinateEndpoint.digit B code j)
        (y (ClearedCoordinateCritical.freeIndex (sweep x F h hh g hg).critical.offset.val
          (fit (sweep x F h hh g hg)).le j))) :
    JoinedIn (slice P (coarse F h) values)
      (i.val∘(FrozenCoordinateOrdering.permutation F.frozen).symm)
      (y∘(FrozenCoordinateOrdering.permutation F.frozen).symm) :=by
  have HC : code=M.code i:=hcode.trans (M.code_anchor i).symm
  have HY : M.curve i endpoint=y:=(M.near i endpoint he y hy).mp (by simpa only [←HC] using hnear)
  have HS : insert endpoint (Ioo a b)⊆Icc a b:=insert_subset he Ioo_subset_Icc_self
  have HP:=(FrontierCover.joinedIn_insert_Ioo he t₀.property).symm
  have HF : ContinuousOn (fun t=>(M.interior.arc i t).val) (insert endpoint (Ioo a b)):=
    continuous_subtype_val.comp_continuousOn ((M.interior.continuous_arc i).mono HS)
  have HJ:=(HP.map HF).mono (by rintro p ⟨t,_,rfl⟩;exact (M.interior.arc i t).property)
  rw [M.readback i t₀.val (Ioo_subset_Icc_self t₀.property),M.anchor i,
    M.readback i endpoint he,HY] at HJ
  exact HJ

include M in
theorem joined_of_rank_near
    (i : IntegralMixedSelectedPhysicalFiber.physical
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ t₀.val)
    (endpoint : ℝ) (he : endpoint∈Icc a b) (y : Fin (n+1)→ℝ)
    (hy : IntegralMixedSelectedCoordinateEndpoint.Frozen
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (sweep x F h hh g hg) φ endpoint y)
    (code : List Bool)
    (hranks : ∀j : IntegralMixedSelectedGeometry.Free (sweep x F h hh g hg),
      IntegralMixedSelectedCoordinateEndpoint.digit B code j=
        (IntegralMixedFrozenFrameSectionCode.ordinal
          (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
          (sweep x F h hh g hg) φ t₀.val i j).val)
    (hnear : ∀j : IntegralMixedSelectedGeometry.Free (sweep x F h hh g hg),
      IntegralMixedSelectedCoordinateEndpoint.Near
        (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
        (sweep x F h hh g hg) φ a b endpoint j
        (IntegralMixedSelectedCoordinateEndpoint.digit B code j)
        (y (ClearedCoordinateCritical.freeIndex (sweep x F h hh g hg).critical.offset.val
          (fit (sweep x F h hh g hg)).le j))) :
    JoinedIn (slice P (coarse F h) values)
      (i.val∘(FrozenCoordinateOrdering.permutation F.frozen).symm)
      (y∘(FrozenCoordinateOrdering.permutation F.frozen).symm) :=by
  apply M.joined_of_near i endpoint he y hy _ rfl
  intro j
  have HD:=IntegralMixedFrozenFrameSectionCode.word_digit
    (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
    (sweep x F h hh g hg) φ t₀.val i j
  change IntegralMixedSelectedCoordinateEndpoint.Near _ _ _ _ _ _ _ j
    (Nat.fromBitsLE (((IntegralMixedFrozenFrameSectionCode.word _ _ _ _ _ i).drop (j.val*B)).take B)) _
  rw [HD,←hranks j]
  exact hnear j

end LeanCanny.Geometry.IntegralMixedFrozenFrame.MatchedSlabInterior
