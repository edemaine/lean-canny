/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCriticalBadSystem
public import LeanCanny.ETR.ComplexCriticalKernelRegular

/-! # Analytic meaning of the bounded Fermat critical certificates

Specializing the direction variables gives the exact finite critical rows
used by native block validators. The evaluated certificate Jacobian is their
analytic derivative determinant; no derivative reader is supplied.
-/

@[expose] public section
namespace LeanCanny.Geometry.FermatCriticalRegularity
open LeanCanny.Algebra LeanCanny.ETR.ComplexCircuit MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem equations_map (low : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (N : ℕ) (v : Fin n → ℝ)
    (i : Fin (n + 1)) :
    (FermatCriticalBadSystem.equations low a N i).map (eval₂Hom (RingHom.id ℝ) v) =
      CriticalKernel.finiteRows (FermatCriticalHomogenization.polynomial low a N) v i := by
  let φ := eval₂Hom (RingHom.id ℝ) v
  let q := FermatCriticalHomogenization.polynomial low a N
  have hφ : φ.comp C = RingHom.id ℝ := by ext r; simp [φ]
  have hp : (q.map C).map φ = q := by rw [map_map, hφ, map_id]
  have hd (j : Fin (n + 1)) : (pderiv j (q.map C)).map φ = pderiv j q := by rw [← pderiv_map, hp]
  rw [FermatCriticalBadSystem.equations_eq]
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [ProjectionCriticalFamily.spatialEquation, ite_true, CriticalKernel.finiteRows, Fin.cons_zero] using hp
  · simp only [ProjectionCriticalFamily.spatialEquation, Fin.succ_ne_zero, ite_false, map_sub, map_mul, map_C,
      Fin.cons_succ, CriticalKernel.finiteRows, eval₂Hom_X']
    change (pderiv j.succ (q.map C)).map φ - C (v j) * (pderiv 0 (q.map C)).map φ =
      pderiv j.succ q - C (v j) * pderiv 0 q
    rw [hd, hd]

theorem jacobian_eval (low : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (N : ℕ) (v : Fin n → ℝ)
    (x : Fin (n + 1) → ℝ) :
    (FermatCriticalBadSystem.jacobian low a N).eval₂ (eval₂Hom (RingHom.id ℝ) v) x =
      (PolynomialSystemRegularity.matrix (RingHom.id ℝ)
        (CriticalKernel.finiteRows (FermatCriticalHomogenization.polynomial low a N) v) x).det := by
  change (eval₂Hom (eval₂Hom (RingHom.id ℝ) v) x) (Matrix.det _) = _
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  change (pderiv j (FermatCriticalBadSystem.equations low a N i)).eval₂ (eval₂Hom (RingHom.id ℝ) v) x = _
  rw [← eval_map, ← pderiv_map, equations_map]
  rfl

theorem regular_of_certificate (low : MvPolynomial (Fin (n + 1)) ℝ) (a : ℝ) (N : ℕ) (v : Fin n → ℝ)
    (x : Fin (n + 1) → ℝ)
    (h : (FermatCriticalBadSystem.jacobian low a N).eval₂ (eval₂Hom (RingHom.id ℝ) v) x ≠ 0) :
    (fderiv ℝ (fun y => fun i =>
      (CriticalKernel.finiteRows (FermatCriticalHomogenization.polynomial low a N) v i).eval y) x).IsInvertible := by
  have H := PolynomialSystemRegularity.isInvertible_iff (RingHom.id ℝ)
    (CriticalKernel.finiteRows (FermatCriticalHomogenization.polynomial low a N) v) x
  simp only [eval₂_id] at H
  exact H.mpr ((jacobian_eval low a N v x) ▸ h)

end LeanCanny.Geometry.FermatCriticalRegularity
