/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotMarginProjection
public import LeanCanny.Geometry.SquaredDistanceFibers
/-! # Actual positive coordinate maxima on compact selected-radius fibers

A selected point on an old-coordinate sphere gives a positive maximum of
the literal initial graph coordinate. Boundary points give such maxima at
arbitrarily small positive squared radii. No polynomial-objective oracle or
critical-root lifting premise occurs in these statements.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotMarginMaxima
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotMarginProjection
open scoped Classical

noncomputable def targetSphere (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ) (r : ℝ) :
    Set (Target c) := {x | SquaredDistanceFibers.value center x.val=r}
noncomputable def sourceSphere (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ) (r : ℝ) :
    Set (Source c) := projection c ⁻¹' targetSphere c center r

theorem compact_targetSphere (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (r : ℝ) (hr : 0≤r) : IsCompact (targetSphere c center r) := by
  rw [Subtype.isCompact_iff]
  have HE : Subtype.val '' targetSphere c center r=
      {x : Fin (FormulaSignSlotSource.dimension c) → ℝ | SquaredDistanceFibers.value center x=r} ∩
      {x | (FormulaSignSlotSource.envelope c).Holds (Formula.extend x)} := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨hy,y.property⟩
    · rintro ⟨hx,hp⟩
      exact ⟨⟨x,hp⟩,hx,rfl⟩
  rw [HE]
  exact (SquaredDistanceFibers.compact_level center r hr).inter_right
    (FormulaSignPartition.closed_holds (FormulaSignSlotSource.envelope_closed c) _)

theorem compact_sourceSphere (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (r : ℝ) (hr : 0≤r) : IsCompact (sourceSphere c center r) :=
  (proper_projection c).isCompact_preimage (compact_targetSphere c center r hr)

theorem positive_maximum (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (x : Target c) (hx : (FormulaSignSlotSource.stratum c).Holds (Formula.extend x.val)) :
    ∃ y : Source c, y∈sourceSphere c center (SquaredDistanceFibers.value center x.val) ∧
      IsMaxOn (value c) (sourceSphere c center (SquaredDistanceFibers.value center x.val)) y ∧ 0 < value c y := by
  obtain ⟨z,hz⟩ := projection_surjective c x
  have HZ : z∈sourceSphere c center (SquaredDistanceFibers.value center x.val) := by
    change SquaredDistanceFibers.value center (projection c z).val=_
    rw [hz]
  have HP : 0 < value c z := (value_positive_iff c z).mpr (by rw [hz]; exact hx)
  obtain ⟨y,hy,HM⟩ := (compact_sourceSphere c center _ (SquaredDistanceFibers.nonneg center x.val)).exists_isMaxOn
    ⟨z,HZ⟩ (continuous_value c).continuousOn
  exact ⟨y,hy,HM,HP.trans_le (HM HZ)⟩

noncomputable def selected (c : List Bool) : Set (Target c) :=
  {x | (FormulaSignSlotSource.stratum c).Holds (Formula.extend x.val)}

theorem arbitrarily_small_maxima (c : List Bool) (x : Target c) (hx : x∈closure (selected c))
    (hnot : x∉selected c) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ ∃ y : Source c, y∈sourceSphere c x.val r ∧
      IsMaxOn (value c) (sourceSphere c x.val r) y ∧ 0 < value c y := by
  let U : Set (Target c) := {z | SquaredDistanceFibers.value x.val z.val < ε}
  have HU : IsOpen U := isOpen_lt
    ((SquaredDistanceFibers.continuous_value x.val).comp continuous_subtype_val) continuous_const
  have HX : x∈U := by
    change SquaredDistanceFibers.value x.val x.val < ε
    simpa [SquaredDistanceFibers.value] using hε
  have HC : x∈closure (selected c∩U) := HU.closure_inter ⟨hx,HX⟩
  obtain ⟨z,hz,hU⟩ := (show (closure (selected c∩U)).Nonempty from ⟨x,HC⟩).of_closure
  have HZ : z≠x := by intro H; subst z; exact hnot hz
  have HR : 0 < SquaredDistanceFibers.value x.val z.val := by
    have HN := SquaredDistanceFibers.nonneg x.val z.val
    have HE : SquaredDistanceFibers.value x.val z.val≠0 := by
      intro H
      exact HZ (Subtype.ext ((SquaredDistanceFibers.zero_iff x.val z.val).mp H))
    exact lt_of_le_of_ne HN (Ne.symm HE)
  obtain ⟨y,hy,HM,HP⟩ := positive_maximum c x.val z hz
  exact ⟨_,HR,hU,y,hy,HM,HP⟩

end LeanCanny.Connectivity.FormulaSignSlotMarginMaxima
