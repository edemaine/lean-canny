/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotCenteredRadialGrid
public import LeanCanny.Geometry.TiltedCoerciveComponentEliminants
/-! # Finite radial samples retain the actual selected positive component

The linear objective tilt retains a positive selected label through the
constructed coercive limits. The coordinate grid has no threshold parameter.
The original spatial tuple and radius are recovered exactly.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotTiltedRadialGrid
open Set ETR LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotMarginProjection FormulaSignSlotMarginMaxima FormulaSignSlotComponentMaxima
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Q (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) := polynomial c a r
noncomputable abbrev OldPositive (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) :=
  TiltedCoerciveComponentSampling.Positive (Q c a r) (marginIndex c)

noncomputable def zeroPoint (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ)
    (x : CoerciveComponentSampling.Zeros (Q c a r)) : Graph c :=
  ⟨x.val,((FormulaSignSlotCenteredRadialLimits.zero_iff c a r x.val).mp x.property).1⟩

theorem zeroPoint_slice (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ)
    (x : CoerciveComponentSampling.Zeros (Q c a r)) : zeroPoint c a r x∈slice c a r :=
  ((FormulaSignSlotCenteredRadialLimits.zero_iff c a r x.val).mp x.property).2

noncomputable def originalPositive (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ)
    (x : OldPositive c a r) : Positive c :=
  ⟨forget c (zeroPoint c a r x.val),by
    rw [← margin_coordinate]
    exact x.property⟩

theorem originalPositive_continuous (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) :
    Continuous (originalPositive c a r) := by
  have HZ : Continuous (zeroPoint c a r) := continuous_subtype_val.subtype_mk _
  exact ((CenteredRadialGraph.oldPoint_continuous _ _ _ (FormulaSignSlotCenteredRadialGraph.scope c)).comp
    (HZ.comp continuous_subtype_val)).subtype_mk _

noncomputable def fromOld (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (x : Positive c)
    (hx : x.val∈sourceSphere c a r) : OldPositive c a r :=
  ⟨⟨(FormulaSignSlotCenteredRadialGraph.lift c a x.val).val,by
    have H := lift_slice c a r x.val hx
    exact (FormulaSignSlotCenteredRadialLimits.zero_iff c a r _).mpr
      ⟨(FormulaSignSlotCenteredRadialGraph.lift c a x.val).property,H.1,H.2⟩⟩,by
    change 0 < (FormulaSignSlotCenteredRadialGraph.lift c a x.val).val (marginIndex c)
    rw [margin_coordinate,forget_lift]
    exact x.property⟩

theorem originalPositive_fromOld (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ)
    (x : Positive c) (hx : x.val∈sourceSphere c a r) : originalPositive c a r (fromOld c a r x hx)=x := by
  apply Subtype.ext
  exact forget_lift c a x.val

theorem fromOld_coordinate (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ)
    (x : Positive c) (hx : x.val∈sourceSphere c a r) : (fromOld c a r x hx).val.val (marginIndex c)=value c x.val := by
  change (FormulaSignSlotCenteredRadialGraph.lift c a x.val).val (marginIndex c)=_
  rw [margin_coordinate,forget_lift]

attribute [local irreducible] Q degreeBudget FormulaSignSlotMargin.initialDimension
  FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialPolynomial

noncomputable def grid (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) :=
  TiltedCoerciveComponentEliminants.grid (Q c a r) (degreeBudget c) (marginIndex c)

theorem finite_grid (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) : (grid c a r).Finite := by
  unfold grid
  have HD : (Q c a r).totalDegree≤degreeBudget c := by
    unfold Q
    exact polynomial_degree c a r
  exact TiltedCoerciveComponentEliminants.finite_grid (n:=N c+d c+1) (Q c a r) (degreeBudget c) HD (marginIndex c)

theorem sample_same_piece (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (hr : 0≤r)
    (C : Set (Positive c)) (hC : IsClopen C) (x : Positive c) (hxC : x∈C)
    (hx : x.val∈sourceSphere c a r) :
    ∃ z : OldPositive c a r, originalPositive c a r z∈C ∧
      value c x.val≤z.val.val (marginIndex c) ∧ z.val.val∈grid c a r := by
  have HC : IsClopen (originalPositive c a r ⁻¹' C) := hC.preimage (originalPositive_continuous c a r)
  have H0 : fromOld c a r x hx∈originalPositive c a r ⁻¹' C := by
    change originalPositive c a r (fromOld c a r x hx)∈C
    rwa [originalPositive_fromOld]
  have HD : (Q c a r).totalDegree≤degreeBudget c := by
    unfold Q
    exact polynomial_degree c a r
  have HK : IsCompact (CoerciveComponentSampling.Zeros (Q c a r)) := by
    unfold Q
    exact compact_zeros c a r hr
  obtain ⟨z,HZ,HU,HG⟩ := TiltedCoerciveComponentEliminants.meets_positive_piece (Q c a r) (degreeBudget c)
    HD (marginIndex c) HK _ HC _ H0
  refine ⟨z,HZ,?_,HG⟩
  rwa [fromOld_coordinate] at HU

theorem sampled_radius (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (z : OldPositive c a r) :
    (originalPositive c a r z).val∈sourceSphere c a r :=
  forget_slice c a r (zeroPoint_slice c a r z.val)

theorem arbitrarily_small_samples (c : List Bool) (C : Set (Positive c)) (hC : IsClopen C)
    (x : Source c) (hx : x∈closure (ambient c C)) (hn : x∉ambient c C) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ ∃ z : OldPositive c (projection c x).val r,
      originalPositive c (projection c x).val r z∈C ∧ z.val.val∈grid c (projection c x).val r ∧
      (originalPositive c (projection c x).val r z).val∈sourceSphere c (projection c x).val r := by
  obtain ⟨r,hr,hεr,y,hy,hyS,_HM,HP⟩ := FormulaSignSlotComponentMaxima.arbitrarily_small_maxima
    c C hC.isClosed x hx hn ε hε
  let yP : Positive c := ⟨y,HP⟩
  have HYC : yP∈C := by
    obtain ⟨w,hw,HE⟩ := hy
    have H : yP=w := Subtype.ext HE.symm
    exact H.symm ▸ hw
  obtain ⟨z,HZ,_HU,HG⟩ := sample_same_piece c (projection c x).val r hr.le C hC yP HYC hyS
  exact ⟨r,hr,hεr,z,HZ,HG,sampled_radius c (projection c x).val r z⟩

end LeanCanny.Connectivity.FormulaSignSlotTiltedRadialGrid
