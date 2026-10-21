/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Determinants of intertwined maps through kernels and ranges

An intertwining square preserves the kernel and range of its connecting
map. The first isomorphism theorem conjugates the induced quotient map to
the range restriction. Over a field, the domain determinant therefore
factors as the kernel determinant times the range determinant.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntertwiningDeterminant
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem kernel_preserved (d : V →ₗ[K] W) (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (h : d.comp f = g.comp d) : LinearMap.ker d ≤ (LinearMap.ker d).comap f := by
  intro x hx
  change d (f x) = 0
  have he := LinearMap.congr_fun h x
  change d (f x) = g (d x) at he
  rw [hx, map_zero] at he
  exact he

theorem range_preserved (d : V →ₗ[K] W) (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (h : d.comp f = g.comp d) : LinearMap.range d ≤ (LinearMap.range d).comap g := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, LinearMap.congr_fun h x⟩

theorem quotient_range_intertwines (d : V →ₗ[K] W) (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (h : d.comp f = g.comp d) :
    d.quotKerEquivRange.toLinearMap.comp ((LinearMap.ker d).mapQ (LinearMap.ker d) f (kernel_preserved d f g h)) =
      (g.restrict (range_preserved d f g h)).comp d.quotKerEquivRange.toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ v =>
    apply Subtype.ext
    exact LinearMap.congr_fun h v

theorem quotient_det_eq_range_det (d : V →ₗ[K] W) (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (h : d.comp f = g.comp d) :
    ((LinearMap.ker d).mapQ (LinearMap.ker d) f (kernel_preserved d f g h)).det =
      (g.restrict (range_preserved d f g h)).det := by
  let e := d.quotKerEquivRange
  have he : g.restrict (range_preserved d f g h) = e.toLinearMap.comp
      (((LinearMap.ker d).mapQ (LinearMap.ker d) f (kernel_preserved d f g h)).comp e.symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun (quotient_range_intertwines d f g h) (e.symm x)
    change e (((LinearMap.ker d).mapQ (LinearMap.ker d) f (kernel_preserved d f g h)) (e.symm x)) =
      (g.restrict (range_preserved d f g h)) (e (e.symm x)) at hx
    rw [e.apply_symm_apply] at hx
    exact hx.symm
  rw [he, LinearMap.det_conj]

theorem determinant [FiniteDimensional K V] (d : V →ₗ[K] W) (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (h : d.comp f = g.comp d) :
    f.det = (f.restrict (kernel_preserved d f g h)).det * (g.restrict (range_preserved d f g h)).det := by
  rw [LinearMap.det_eq_det_mul_det (LinearMap.ker d) f (kernel_preserved d f g h),
    quotient_det_eq_range_det d f g h]

theorem restriction_det_congr (U T : Submodule K V) (he : U = T) (f : V →ₗ[K] V)
    (hU : U ≤ U.comap f) (hT : T ≤ T.comap f) : (f.restrict hU).det = (f.restrict hT).det := by
  subst T
  rfl

theorem restriction_det_eq_of_top (U : Submodule K V) (he : U = ⊤) (f : V →ₗ[K] V)
    (hf : U ≤ U.comap f) : (f.restrict hf).det = f.det := by
  subst U
  let e : (⊤ : Submodule K V) ≃ₗ[K] V := Submodule.topEquiv
  have hc : e.toLinearMap.comp ((f.restrict hf).comp e.symm.toLinearMap) = f := by
    apply LinearMap.ext
    intro x
    rfl
  rw [← LinearMap.det_conj (f.restrict hf) e, hc]

end LeanCanny.Algebra.IntertwiningDeterminant
