/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointSquarefreeIndexRetention
public import LeanCanny.Encoding.FormulaSignSlotRadialJointHeadIntervalRetention
public import LeanCanny.Algebra.DomainSquarefreeLeadingCoefficient
public import LeanCanny.Geometry.RealParameterRootBranches
/-! # Actual root-branch cuts retain their open-interval avoidance on a stratum -/
@[expose] public section
namespace LeanCanny.Geometry.RealParameterRootBranches
open LeanCanny.Algebra Polynomial PrincipalSubresultant Set
noncomputable def NoRoots (p:ℝ[X]) (b:ℝ):Prop:=∀r,p.eval r=0 → r ∉ Ioo 0 b
private theorem cut_zero (p:Polynomial (Polynomial ℝ)) (hp:p.natDegree≠0) (r:ℝ):
    (cut p).eval r=0 ↔ p.leadingCoeff.eval r=0 ∨
      (psc p p.derivative p.natDegree (p.natDegree-1) (DomainSquarefree.index p)).eval r=0:=by
  rw [cut,auxiliary,DomainSquarefree.exceptional,ite_eq_right hp,DomainSquarefree.leading_coefficient p hp]
  simp only [Polynomial.eval_mul,Polynomial.eval_pow]
  by_cases HA:p.leadingCoeff.eval r=0
  · simp only [HA,zero_mul,true_or]
  · by_cases HB:(psc p p.derivative p.natDegree (p.natDegree-1) (DomainSquarefree.index p)).eval r=0
    · simp only [HB,mul_zero,zero_mul,or_true]
    · simp only [mul_eq_zero,HA,HB,false_or,pow_ne_zero _ HB]

theorem cut_no_roots_iff (p:Polynomial (Polynomial ℝ)) (b:ℝ):
    NoRoots (cut p) b ↔ NoRoots p.leadingCoeff b ∧
      (p.natDegree=0 ∨ NoRoots (psc p p.derivative p.natDegree (p.natDegree-1) (DomainSquarefree.index p)) b):=by
  by_cases hp:p.natDegree=0
  · have HE:cut p=p.leadingCoeff:=by
      simp only [cut,auxiliary,DomainSquarefree.exceptional,DomainSquarefree.polynomial,hp,ite_true,
        Polynomial.leadingCoeff_one,mul_one]
    simp only [HE,hp,true_or,and_true]
  · constructor
    · intro H
      refine ⟨?_,Or.inr ?_⟩
      · intro r hr
        exact H r ((cut_zero p hp r).mpr (Or.inl hr))
      · intro r hr
        exact H r ((cut_zero p hp r).mpr (Or.inr hr))
    · rintro ⟨HL,HD|HS⟩
      · exact (hp HD).elim
      · intro r hr
        rcases (cut_zero p hp r).mp hr with HA|HB
        · exact HL r HA
        · exact HS r HB
theorem no_bad_iff {ι:Type*} (p:ι→Polynomial (Polynomial ℝ)) (b:ℝ):
    (∀r∈Ioo 0 b,r ∉ bad p) ↔ ∀i,NoRoots (cut (p i)) b:=by
  constructor
  · intro H i r hr hrI
    exact H r hrI ⟨i,hr⟩
  · intro H r hr ⟨i,hi⟩
    exact H i r hi hr

end LeanCanny.Geometry.RealParameterRootBranches

namespace LeanCanny.Encoding.FormulaSignSlotRadialJointBranchCutRetention
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity Polynomial PrincipalSubresultant Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "Space"=>FormulaSignSlotRadialJointStratumLabels.Space
local notation "S"=>FormulaSignSlotRadialJointStratum.source
local notation "env"=>FormulaSignSlotRadialJointDescriptorGeometry.environment
local notation "radial"=>FormulaSignSlotRadialJointPrincipalWindowRetention.radial
local notation "raw"=>FormulaSignSlotRadialJointPrincipalWindowRetention.raw
local notation "Raw"=>FormulaSignSlotRadialPrincipalRadiusSource.source
local notation "N"=>FormulaSignSlotRadialCutWindowSources.principalCenters
local notation "hd"=>FormulaSignSlotRadialCutWindowSources.principal_dimension
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialParameterEliminant.coordinate

private theorem signed_interval (p:Polynomial (Polynomial ℝ)) (d k:ℕ) (hk:k<d) (b:ℝ):
    RealParameterRootBranches.NoRoots (signedPsc p p.derivative d (d-1) k) b ↔
      RealParameterRootBranches.NoRoots (psc p p.derivative d (d-1) k) b:=by
  have HJ:k≤min d (d-1):=by omega
  unfold RealParameterRootBranches.NoRoots
  apply forall_congr'
  intro r
  rw [signedPsc_of_le p p.derivative HJ,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_neg,Polynomial.eval_one]
  rw [mul_eq_zero,or_iff_right (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))]

private theorem principal_interval (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (j:Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c)))
    (t d k:ℕ)
    (HX:FormulaSignSlotRadialCenterSquarefreeSelection.Guards (radial c j.val) (fun i=>env c x (4*i.val)) t d k)
    (HY:FormulaSignSlotRadialCenterSquarefreeSelection.Guards (radial c j.val) (fun i=>env c y (4*i.val)) t d k)
    (hk:k<d):
    RealParameterRootBranches.NoRoots
      (psc (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radial c j.val) (fun i=>env c x (4*i.val)))
        (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radial c j.val) (fun i=>env c x (4*i.val))).derivative
        d (d-1) k) (env c x 3) ↔
    RealParameterRootBranches.NoRoots
      (psc (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radial c j.val) (fun i=>env c y (4*i.val)))
        (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radial c j.val) (fun i=>env c y (4*i.val))).derivative
        d (d-1) k) (env c y 3):=by
  have ht:=HX.1.1
  have hD:=HX.1.2.1
  change t ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound (radial c j.val) at ht
  change d ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound (radial c j.val) at hD
  have HBx:0<env c x 3:=(FormulaSignSlotRadialJointDescriptorGeometry.radius_bounds c x).1.trans
    (FormulaSignSlotRadialJointDescriptorGeometry.radius_bounds c x).2
  have HBy:0<env c y 3:=(FormulaSignSlotRadialJointDescriptorGeometry.radius_bounds c y).1.trans
    (FormulaSignSlotRadialJointDescriptorGeometry.radius_bounds c y).2
  have HI:=IntegralPolynomialWindowTarski.interval_iff_of_signs Raw N hd (raw c j.val t d k)
    (env c x 3) (fun i=>env c x (4*i.val)) (env c y 3) (fun i=>env c y (4*i.val))
    (FormulaSignSlotRadialJointPrincipalWindowRetention.catalogue_signs c x y h j t d k ht hD (by omega)) HBx HBy
  dsimp only [FormulaSignSlotRadialJointPrincipalWindowRetention.raw] at HI
  rw [FormulaSignSlotRadialJointSquarefreeIndexRetention.principal_polynomial _ _ _ _ _ HX.1,
    FormulaSignSlotRadialJointSquarefreeIndexRetention.principal_polynomial _ _ _ _ _ HY.1] at HI
  exact (signed_interval _ d k hk _).symm.trans (HI.trans (signed_interval _ d k hk _))

/-- The genuine selected squarefree cut is preserved; no selected index or guard is supplied. -/
theorem cut_interval_iff_of_joined (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (j:Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c))):
    RealParameterRootBranches.NoRoots
      (RealParameterRootBranches.cut (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radial c j.val)
        (fun i=>env c x (4*i.val)))) (env c x 3) ↔
    RealParameterRootBranches.NoRoots
      (RealParameterRootBranches.cut (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radial c j.val)
        (fun i=>env c y (4*i.val)))) (env c y 3):=by
  obtain ⟨t,_,d,_,k,_,HX⟩:=FormulaSignSlotRadialCenterSquarefreeSelection.exists_guards
    (radial c j.val) (fun i=>env c x (4*i.val))
  have HY:=(FormulaSignSlotRadialJointSquarefreeIndexRetention.guards_iff_of_joined c x y h j t d k).mp HX
  have HDx:=FormulaSignSlotRadialCenterSquarefreeSelection.coordinate_degree _ _ t d HX.1
  have HDy:=FormulaSignSlotRadialCenterSquarefreeSelection.coordinate_degree _ _ t d HY.1
  have HKx:=(FormulaSignSlotRadialCenterSquarefreeSelection.guards_iff _ _ t d k).mp HX |>.2
  have HKy:=(FormulaSignSlotRadialCenterSquarefreeSelection.guards_iff _ _ t d k).mp HY |>.2
  rw [RealParameterRootBranches.cut_no_roots_iff,RealParameterRootBranches.cut_no_roots_iff]
  apply and_congr
  · exact FormulaSignSlotRadialJointHeadIntervalRetention.leading_interval_iff_of_joined c x y h j.val j.isLt
  · rw [HDx,HDy,←HKx,←HKy]
    by_cases HD:d=0
    · simp only [HD,true_or]
    · rw [or_iff_right HD,or_iff_right HD]
      exact principal_interval c x y h j t d k HX HY
        (by have H:=HX.2;rw [ite_eq_right HD] at H;exact H.1)

/-- Literal parameter-coordinate cuts have the same interval truth at both centers. -/
theorem actual_cut_interval_iff_of_joined (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (j:Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c))):
    RealParameterRootBranches.NoRoots
      (RealParameterRootBranches.cut (FormulaSignSlotRadialParameterEliminant.coordinate
        (FormulaSignSlotRadialJointHeadIntervalRetention.root c)
        (FormulaSignSlotRadialJointDescriptorGeometry.center c x) j))
      (FormulaSignSlotRadialJointDescriptorGeometry.bound c x) ↔
    RealParameterRootBranches.NoRoots
      (RealParameterRootBranches.cut (FormulaSignSlotRadialParameterEliminant.coordinate
        (FormulaSignSlotRadialJointHeadIntervalRetention.root c)
        (FormulaSignSlotRadialJointDescriptorGeometry.center c y) j))
      (FormulaSignSlotRadialJointDescriptorGeometry.bound c y):=by
  have HI:=cut_interval_iff_of_joined c x y h j
  have EX:FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radial c j.val)
      (fun i=>env c x (4*i.val))=FormulaSignSlotRadialParameterEliminant.coordinate
        (FormulaSignSlotRadialJointHeadIntervalRetention.root c)
        (FormulaSignSlotRadialJointDescriptorGeometry.center c x) j:=
    FormulaSignSlotRadialJointHeadIntervalRetention.actual_coordinate c x j
  have EY:FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radial c j.val)
      (fun i=>env c y (4*i.val))=FormulaSignSlotRadialParameterEliminant.coordinate
        (FormulaSignSlotRadialJointHeadIntervalRetention.root c)
        (FormulaSignSlotRadialJointDescriptorGeometry.center c y) j:=
    FormulaSignSlotRadialJointHeadIntervalRetention.actual_coordinate c y j
  rw [EX,EY] at HI
  exact HI

/-- The whole finite cut set used by the actual root-branch theorem is preserved. -/
theorem bad_interval_iff_of_joined (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val):
    (∀r∈Ioo 0 (FormulaSignSlotRadialJointDescriptorGeometry.bound c x),
      r ∉ RealParameterRootBranches.bad (FormulaSignSlotRadialParameterEliminant.coordinate
        (FormulaSignSlotRadialJointHeadIntervalRetention.root c)
        (FormulaSignSlotRadialJointDescriptorGeometry.center c x))) ↔
    (∀r∈Ioo 0 (FormulaSignSlotRadialJointDescriptorGeometry.bound c y),
      r ∉ RealParameterRootBranches.bad (FormulaSignSlotRadialParameterEliminant.coordinate
        (FormulaSignSlotRadialJointHeadIntervalRetention.root c)
        (FormulaSignSlotRadialJointDescriptorGeometry.center c y))):=by
  rw [RealParameterRootBranches.no_bad_iff,RealParameterRootBranches.no_bad_iff]
  exact forall_congr' (fun j=>actual_cut_interval_iff_of_joined c x y h j)

end LeanCanny.Encoding.FormulaSignSlotRadialJointBranchCutRetention
