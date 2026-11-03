/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleOrdinalNaturality
/-! # Complete vertex labels under literal composition of all input fields -/
@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteNaturality
open LeanCanny.Algebra LeanCanny.Computation SquareSampleInput
open scoped Classical
attribute [local irreducible] SquareSampleParameters.decode SquareSampleHashEnumeration.root

theorem grid_comp (F : Inputs) (f : List Bool→List Bool) :
    SquareSampleGrid.input (comp F f)=comp (SquareSampleGrid.input F) f :=rfl

theorem width_comp (F : Inputs) (f : List Bool→List Bool) (u : List Bool) :
    SquareSampleVertices.width (comp F f) u=SquareSampleVertices.width F (f u) :=rfl

theorem valid_comp (F : Inputs) (f : List Bool→List Bool) (u w : List Bool) :
    SquareSampleVertices.Valid (comp F f) u w↔SquareSampleVertices.Valid F (f u) w :=by
  have HC:=SquareSampleRankNaturality.count_congr (comp F f) F u (f u)
    (SquareSampleParameterNaturality.roots_comp F f u)
  simp only [SquareSampleVertices.Valid,width_comp,HC]

theorem sample_point (F : Inputs) (u w : List Bool) (hw : SquareSampleVertices.Valid F u w) :
    (SquareSampleVertices.sample F u w hw).val.val=
      SquareSampleParameters.decode F u
        (SquareSampleHashEnumeration.root F u ⟨Nat.fromBitsLE w,hw.2⟩).val :=rfl

theorem sample_comp (F : Inputs) (f : List Bool→List Bool) (u w : List Bool)
    (hw : SquareSampleVertices.Valid (comp F f) u w)
    (hv : SquareSampleVertices.Valid F (f u) w) :
    (SquareSampleVertices.sample (comp F f) u w hw).val.val=
      (SquareSampleVertices.sample F (f u) w hv).val.val :=by
  rw [sample_point,sample_point]
  have HE:=SquareSampleOrdinalNaturality.root_val_comp F f u
    ⟨Nat.fromBitsLE w,hw.2⟩ ⟨Nat.fromBitsLE w,hv.2⟩ rfl
  rw [HE]
  exact SquareSampleParameterNaturality.decode_comp F f u _
    ((SquareSampleQueries.mem_roots F (f u) _).mp
      (SquareSampleHashEnumeration.root F (f u) ⟨Nat.fromBitsLE w,hv.2⟩).property).1

theorem complete_width_comp (F : Inputs) (f : List Bool→List Bool) (u : List Bool) :
    SquareSampleCompleteVertices.width (comp F f) u=SquareSampleCompleteVertices.width F (f u) :=by
  change SquareSampleVertices.width (SquareSampleGrid.input (comp F f)) u=_
  rw [grid_comp,width_comp]
  rfl

theorem point_comp (F : Inputs) (f : List Bool→List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.GridValid (comp F f) u w)
    (hv : SquareSampleCompleteVertices.GridValid F (f u) w) :
    SquareSampleCompleteVertices.point (comp F f) u w hw=
      SquareSampleCompleteVertices.point F (f u) w hv :=by
  unfold SquareSampleCompleteVertices.point
  exact sample_comp (SquareSampleGrid.input F) f u w hw hv

theorem complete_valid_comp (F : Inputs) (f : List Bool→List Bool) (u w : List Bool) :
    SquareSampleCompleteVertices.Valid (comp F f) u w↔SquareSampleCompleteVertices.Valid F (f u) w :=by
  have HG : SquareSampleCompleteVertices.GridValid (comp F f) u w↔
      SquareSampleCompleteVertices.GridValid F (f u) w:=by
    change SquareSampleVertices.Valid (SquareSampleGrid.input (comp F f)) u w↔_
    rw [grid_comp]
    exact valid_comp (SquareSampleGrid.input F) f u w
  constructor
  · rintro ⟨hw,hz⟩
    refine ⟨HG.mp hw,?_⟩
    have HE:=point_comp F f u w hw (HG.mp hw)
    rw [HE] at hz
    exact hz
  · rintro ⟨hv,hz⟩
    refine ⟨HG.mpr hv,?_⟩
    have HE:=point_comp F f u w (HG.mpr hv) hv
    rw [HE]
    exact hz

theorem candidate_comp (F : Inputs) (f : List Bool→List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (comp F f) u w)
    (hv : SquareSampleCompleteVertices.Valid F (f u) w) :
    (SquareSampleCompleteVertices.candidate (comp F f) u w hw).val=
      (SquareSampleCompleteVertices.candidate F (f u) w hv).val :=
  point_comp F f u w (Classical.choose hw) (Classical.choose hv)

end LeanCanny.Encoding.SquareSampleCompleteNaturality
