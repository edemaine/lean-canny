/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.BoundedMarkedCoordinates

/-! # The canonical marked lift has two real slack coordinates

These identities concern the prescribed lift of one original point. They
make no claim that an arbitrary critical point above it is marked.
-/
@[expose] public section
namespace LeanCanny.Geometry.PurePowerSublevelLift
open scoped Classical

theorem section_im_zero {X : Type*} [TopologicalSpace X] (m : ℕ) (hm : Odd m) (g : X→ℝ) (e : ℝ)
    (x : CircleSublevelLift.Base g e) : (sectionMap m hm g e x).val.2.im=0 := by
  change (realPower m hm).symm (0 : ℝ)=0
  apply (realPower m hm).injective
  have HM : m≠0 := by obtain ⟨k,HK⟩:=hm; omega
  rw [Homeomorph.apply_symm_apply,realPower_apply,zero_pow HM]

end LeanCanny.Geometry.PurePowerSublevelLift

namespace LeanCanny.Geometry.BoundedRegularSource
open LeanCanny.Algebra BoundedZeroSource
open scoped BigOperators Classical
variable {n : ℕ}

noncomputable def sphereSlack (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (x : Bounded q R) : ℝ :=
  Real.sqrt ((radiusSquared R : ℝ)-radial x.val)

noncomputable def regularSlack (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (x : Bounded q R) : ℂ :=
  (PurePowerSublevelLift.sectionMap (powerHalfDegree D) (powerHalfDegree_odd D)
    (scaledEnergy q D b R) (level n D b R) (basePoint q D b R x)).val.2

theorem sphereSlack_sq (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (x : Bounded q R) :
    sphereSlack q R x^2=(radiusSquared R : ℝ)-radial x.val :=
  Real.sq_sqrt (sub_nonneg.mpr x.property.2)

theorem regularSlack_im (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (x : Bounded q R) :
    (regularSlack q D b R x).im=0 := PurePowerSublevelLift.section_im_zero _ _ _ _ _

theorem section_coordinates (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (x : Bounded q R) :
    (BoundedZeroSource.sectionMap q R x).val=Fin.append x.val ![sphereSlack q R x,0] := rfl

theorem lift_coordinates (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (x : Bounded q R) :
    (lift q D b R x).val=Fin.append (Fin.append x.val ![sphereSlack q R x,0]) ![(regularSlack q D b R x).re,0] := by
  change Fin.append (BoundedZeroSource.sectionMap q R x).val
    ![(regularSlack q D b R x).re,(regularSlack q D b R x).im]=_
  rw [section_coordinates,regularSlack_im]

theorem regularSlack_sum (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (x : Bounded q R) :
    (∑ i : Fin n,x.val i^powerDegree D)+(sphereSlack q R x)^powerDegree D+
      (regularSlack q D b R x).re^powerDegree D=level n D b R := by
  have HD : powerDegree D≠0 := by have H:=powerDegree_gt_one D; omega
  have HE : scaledEnergy q D b R (BoundedZeroSource.sectionMap q R x).val+
      ((regularSlack q D b R x).re^powerDegree D+(regularSlack q D b R x).im^powerDegree D)=level n D b R :=
    (PurePowerSublevelLift.sectionMap (powerHalfDegree D) (powerHalfDegree_odd D)
      (scaledEnergy q D b R) (level n D b R) (basePoint q D b R x)).property
  rw [regularSlack_im,zero_pow HD,add_zero,scaledEnergy,(BoundedZeroSource.sectionMap q R x).property,
    mul_zero,zero_add,section_coordinates,Fin.sum_univ_add] at HE
  simpa only [Fin.append_left,Fin.append_right,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    zero_pow HD,add_zero] using HE

theorem regularSlack_scaled (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (x : Bounded q R) :
    (2 : ℝ)^regularizationExponent n D b R*(regularSlack q D b R x).re^powerDegree D=
      (2 : ℝ)^regularizationExponent n D b R*(2 : ℝ)^penaltyExponent n D R+1-
        (2 : ℝ)^regularizationExponent n D b R*(∑ i : Fin n,x.val i^powerDegree D)-
        (2 : ℝ)^regularizationExponent n D b R*(sphereSlack q R x)^powerDegree D := by
  have H:=regularSlack_sum q D b R x
  unfold level at H
  have HD : (2 : ℝ)^regularizationExponent n D b R*
      InfinitesimalSign.dyadic (regularizationExponent n D b R)=1 := by
    unfold InfinitesimalSign.dyadic
    exact mul_inv_cancel₀ (by positivity)
  have HM:=congrArg (fun a : ℝ=>(2 : ℝ)^regularizationExponent n D b R*a) H
  simp only [mul_add,HD] at HM
  linear_combination HM

theorem lift_original_coordinate (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (x : Bounded q R) (i : Fin n) :
    (lift q D b R x).val (i.castAdd 4)=x.val i := by
  have H:=congrArg (fun z : Bounded q R=>z.val i) (markedProjection_lift q D b R x)
  rw [markedProjection_apply] at H
  exact H

end LeanCanny.Geometry.BoundedRegularSource
