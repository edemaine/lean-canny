/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FermatLevelSheet
public import Mathlib.Topology.Algebra.MvPolynomial

/-! # Projection identifies the bounded level sheet with its actual region

The projected region is W(x) in the range of A*v-v^d on [-1,1]. It is NOT an
original zero set, nor is it replaced by the smaller symmetric capacity region.
Projection and its inverse retain every original coordinate literally.
-/
@[expose] public section
namespace LeanCanny.Geometry.FermatLevelSheet
open LeanCanny.Algebra MvPolynomial Set
open scoped Topology
variable {n : ℕ}

noncomputable def region (P : IntegralMixedHistory.SpatialSource n) (A : ℤ) : Set (Fin (n+1) → ℝ) :=
  {x | (FermatLevelLift.polynomial P).eval₂ (Int.castRingHom ℝ) x∈range (boundedForward P.degree A)}

noncomputable def sheet (P : IntegralMixedHistory.SpatialSource n) (A : ℤ) : Set (Fin (n+2) → ℝ) :=
  {z | z (Fin.last (n+1))∈Icc (-1:ℝ) 1 ∧
    (FermatLevelLift.polynomial (FermatLevelLift.source P A)).eval₂ (Int.castRingHom ℝ) z=0}

theorem snoc_restrict (z : Fin (n+2) → ℝ) : Fin.snoc (z ∘ Fin.castSucc) (z (Fin.last (n+1)))=z := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact Fin.snoc_last _ _
  · exact Fin.snoc_castSucc _ _ _

theorem inverse_forward (d : ℕ) (A : ℤ) (hA : (d:ℝ)<(A:ℝ)) (w : range (boundedForward d A)) :
    boundedForward d A ((rangeHomeomorph d A hA).symm w)=w.val := by
  have H := congrArg Subtype.val ((rangeHomeomorph d A hA).apply_symm_apply w)
  exact H

noncomputable def lift (P : IntegralMixedHistory.SpatialSource n) (A : ℤ) (hP : P.leading=1)
    (hA : (P.degree:ℝ)<(A:ℝ)) : region P A → sheet P A := fun x =>
  let v := (rangeHomeomorph P.degree A hA).symm ⟨(FermatLevelLift.polynomial P).eval₂ (Int.castRingHom ℝ) x.val,x.property⟩
  ⟨Fin.snoc x.val v.val,by
    refine ⟨by simpa only [Fin.snoc_last] using v.property,?_⟩
    rw [FermatLevelLift.eval_source,hP,Int.cast_one,one_mul]
    have H := inverse_forward P.degree A hA
      ⟨(FermatLevelLift.polynomial P).eval₂ (Int.castRingHom ℝ) x.val,x.property⟩
    change (A:ℝ)*v.val-v.val^P.degree=(FermatLevelLift.polynomial P).eval₂ (Int.castRingHom ℝ) x.val at H
    linarith⟩

noncomputable def project (P : IntegralMixedHistory.SpatialSource n) (A : ℤ) (hP : P.leading=1) :
    sheet P A → region P A := fun z =>
  ⟨z.val ∘ Fin.castSucc,by
    refine ⟨⟨z.val (Fin.last (n+1)),z.property.1⟩,?_⟩
    have H := FermatLevelLift.eval_source P A (z.val ∘ Fin.castSucc) (z.val (Fin.last (n+1)))
    rw [snoc_restrict,hP,Int.cast_one,one_mul,z.property.2] at H
    change (A:ℝ)*z.val (Fin.last (n+1))-z.val (Fin.last (n+1))^P.degree=_
    linarith⟩

theorem project_lift (P : IntegralMixedHistory.SpatialSource n) (A : ℤ) (hP : P.leading=1)
    (hA : (P.degree:ℝ)<(A:ℝ)) (x : region P A) : project P A hP (lift P A hP hA x)=x := by
  apply Subtype.ext
  funext i
  simp only [project,lift,Function.comp_def,Fin.snoc_castSucc]

theorem lift_project (P : IntegralMixedHistory.SpatialSource n) (A : ℤ) (hP : P.leading=1)
    (hA : (P.degree:ℝ)<(A:ℝ)) (z : sheet P A) : lift P A hP hA (project P A hP z)=z := by
  let x := project P A hP z
  let w : range (boundedForward P.degree A) :=
    ⟨(FermatLevelLift.polynomial P).eval₂ (Int.castRingHom ℝ) x.val,x.property⟩
  have HV : (rangeHomeomorph P.degree A hA).symm w=⟨z.val (Fin.last (n+1)),z.property.1⟩ := by
    apply boundedForward_injective P.degree A hA
    rw [inverse_forward]
    have H := FermatLevelLift.eval_source P A (z.val ∘ Fin.castSucc) (z.val (Fin.last (n+1)))
    rw [snoc_restrict,hP,Int.cast_one,one_mul,z.property.2] at H
    change (FermatLevelLift.polynomial P).eval₂ (Int.castRingHom ℝ) (z.val ∘ Fin.castSucc)=
      (A:ℝ)*z.val (Fin.last (n+1))-z.val (Fin.last (n+1))^P.degree
    linarith
  apply Subtype.ext
  change Fin.snoc (z.val ∘ Fin.castSucc) ((rangeHomeomorph P.degree A hA).symm w).val=z.val
  rw [HV]
  exact snoc_restrict z.val

theorem continuous_project (P : IntegralMixedHistory.SpatialSource n) (A : ℤ) (hP : P.leading=1) :
    Continuous (project P A hP) :=
  (continuous_pi fun i => (continuous_apply i.castSucc).comp continuous_subtype_val).subtype_mk _

theorem continuous_lift (P : IntegralMixedHistory.SpatialSource n) (A : ℤ) (hP : P.leading=1)
    (hA : (P.degree:ℝ)<(A:ℝ)) : Continuous (lift P A hP hA) := by
  have HW : Continuous (fun x : region P A => (FermatLevelLift.polynomial P).eval₂ (Int.castRingHom ℝ) x.val) := by
    have H : Continuous (fun x : region P A => ((FermatLevelLift.polynomial P).map (Int.castRingHom ℝ)).eval x.val) :=
      ((FermatLevelLift.polynomial P).map (Int.castRingHom ℝ)).continuous_eval.comp continuous_subtype_val
    simpa only [eval_map] using H
  have HI : Continuous (fun x : region P A =>
      (⟨(FermatLevelLift.polynomial P).eval₂ (Int.castRingHom ℝ) x.val,x.property⟩ : range (boundedForward P.degree A))) :=
    HW.subtype_mk _
  have HV := continuous_subtype_val.comp ((rangeHomeomorph P.degree A hA).symm.continuous.comp HI)
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [lift,Fin.snoc_last,Function.comp_def] using HV
  · simpa only [lift,Fin.snoc_castSucc,Function.comp_def] using
      ((continuous_apply j).comp continuous_subtype_val : Continuous (fun x : region P A => x.val j))

noncomputable def projectionHomeomorph (P : IntegralMixedHistory.SpatialSource n) (A : ℤ)
    (hP : P.leading=1) (hA : (P.degree:ℝ)<(A:ℝ)) : region P A ≃ₜ sheet P A where
  toFun := lift P A hP hA
  invFun := project P A hP
  left_inv := project_lift P A hP hA
  right_inv := lift_project P A hP hA
  continuous_toFun := continuous_lift P A hP hA
  continuous_invFun := continuous_project P A hP

theorem capacity_subset_region (P : IntegralMixedHistory.SpatialSource n) (A : ℤ) (hd : Even P.degree) :
    {x | |(FermatLevelLift.polynomial P).eval₂ (Int.castRingHom ℝ) x|≤(A:ℝ)-1}⊆region P A := by
  intro x hx
  exact values_subset_range P.degree A hd hx

end LeanCanny.Geometry.FermatLevelSheet
