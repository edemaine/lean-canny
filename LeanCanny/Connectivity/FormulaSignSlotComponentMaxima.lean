/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotMarginMaxima
/-! # Positive coordinate maxima retain a relatively closed selected component

Maximization is confined to the closure of the chosen piece. A positive
maximizer belongs to that same piece, so a different component of the same
sign stratum cannot be substituted at a boundary.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotComponentMaxima
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotMarginProjection FormulaSignSlotMarginMaxima
open scoped Classical

noncomputable abbrev Positive (c : List Bool) := {y : Source c // 0 < value c y}
noncomputable def ambient (c : List Bool) (s : Set (Positive c)) : Set (Source c) := Subtype.val '' s

theorem ambient_positive (c : List Bool) (s : Set (Positive c)) {y : Source c} (hy : y∈ambient c s) :
    0 < value c y := by obtain ⟨z,_,rfl⟩ := hy; exact z.property

theorem closure_inside (c : List Bool) (s : Set (Positive c)) (hs : IsClosed s)
    {y : Source c} (hy : y∈closure (ambient c s)) (hp : 0 < value c y) : y∈ambient c s := by
  let z : Positive c := ⟨y,hp⟩
  have HZ : z∈closure s := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    exact hy
  exact ⟨z,hs.closure_eq ▸ HZ,rfl⟩

theorem boundary_zero (c : List Bool) (s : Set (Positive c)) (hs : IsClosed s)
    {x : Source c} (hx : x∈closure (ambient c s)) (hn : x∉ambient c s) : value c x=0 := by
  have HP : ¬0 < value c x := fun H => hn (closure_inside c s hs hx H)
  have HN := value_nonneg c x
  linarith

noncomputable def constrained (c : List Bool) (s : Set (Positive c))
    (center : Fin (FormulaSignSlotSource.dimension c) → ℝ) (r : ℝ) : Set (Source c) :=
  sourceSphere c center r ∩ closure (ambient c s)

theorem compact_constrained (c : List Bool) (s : Set (Positive c))
    (center : Fin (FormulaSignSlotSource.dimension c) → ℝ) (r : ℝ) (hr : 0≤r) :
    IsCompact (constrained c s center r) := (compact_sourceSphere c center r hr).inter_right isClosed_closure

theorem positive_maximum (c : List Bool) (s : Set (Positive c)) (hs : IsClosed s)
    (center : Fin (FormulaSignSlotSource.dimension c) → ℝ) (z : Source c) (hz : z∈ambient c s) :
    ∃ y : Source c, y∈ambient c s ∧
      y∈sourceSphere c center (SquaredDistanceFibers.value center (projection c z).val) ∧
      IsMaxOn (value c) (constrained c s center (SquaredDistanceFibers.value center (projection c z).val)) y ∧
      0 < value c y := by
  have HZ : z∈constrained c s center (SquaredDistanceFibers.value center (projection c z).val) :=
    ⟨rfl,subset_closure hz⟩
  obtain ⟨y,hy,HM⟩ := (compact_constrained c s center _
    (SquaredDistanceFibers.nonneg center (projection c z).val)).exists_isMaxOn ⟨z,HZ⟩ (continuous_value c).continuousOn
  have HP : 0 < value c y := (ambient_positive c s hz).trans_le (HM HZ)
  exact ⟨y,closure_inside c s hs hy.2 HP,hy.1,HM,HP⟩

theorem arbitrarily_small_maxima (c : List Bool) (s : Set (Positive c)) (hs : IsClosed s)
    (x : Source c) (hx : x∈closure (ambient c s)) (hn : x∉ambient c s) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ ∃ y : Source c, y∈ambient c s ∧
      y∈sourceSphere c (projection c x).val r ∧
      IsMaxOn (value c) (constrained c s (projection c x).val r) y ∧ 0 < value c y := by
  let center := (projection c x).val
  let U : Set (Source c) := {z | SquaredDistanceFibers.value center (projection c z).val < ε}
  have HU : IsOpen U := isOpen_lt ((SquaredDistanceFibers.continuous_value center).comp
    (continuous_subtype_val.comp (proper_projection c).continuous)) continuous_const
  have HX : x∈U := by
    change SquaredDistanceFibers.value center center < ε
    simpa [SquaredDistanceFibers.value] using hε
  have HC : x∈closure (ambient c s∩U) := HU.closure_inter ⟨hx,HX⟩
  obtain ⟨z,hz,hU⟩ := (show (closure (ambient c s∩U)).Nonempty from ⟨x,HC⟩).of_closure
  have H0 := boundary_zero c s hs hx hn
  have HR : 0 < SquaredDistanceFibers.value center (projection c z).val := by
    have HN := SquaredDistanceFibers.nonneg center (projection c z).val
    have HE : SquaredDistanceFibers.value center (projection c z).val≠0 := by
      intro H
      have HP := (SquaredDistanceFibers.zero_iff center (projection c z).val).mp H
      have HV : value c z=value c x := by rw [value_eq,value_eq,HP]
      have HZ := ambient_positive c s hz
      rw [HV,H0] at HZ
      exact lt_irrefl _ HZ
    exact lt_of_le_of_ne HN (Ne.symm HE)
  obtain ⟨y,hy,hyS,HM,HP⟩ := positive_maximum c s hs center z hz
  exact ⟨_,HR,hU,y,hy,hyS,HM,HP⟩

end LeanCanny.Connectivity.FormulaSignSlotComponentMaxima
