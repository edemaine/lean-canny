/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCriticalKernelFinite
public import LeanCanny.Geometry.PolynomialSystemRegularity

/-! # Kernel-chart emptiness implies analytic simplicity

The integer critical equations used by the circuit queries form a square
system. Empty complex kernel charts exclude singular real roots of that
same system, giving analytic invertibility without a supplied Jacobian test.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.CriticalKernel
open MvPolynomial LeanCanny.Algebra LeanCanny.Geometry
open scoped Classical BigOperators Matrix

variable {n : ℕ}

noncomputable def finiteRows {R : Type*} [CommRing R] (p : MvPolynomial (Fin (n + 1)) R)
    (w : Fin n → R) : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R :=
  Fin.cons p (fun j => pderiv j.succ p - C (w j) * pderiv 0 p)

theorem finite_bad_iff_kernel {R : Type*} [CommRing R] (φ : R →+* ℂ)
    (p : MvPolynomial (Fin (n + 1)) R) (v : ℕ → ℤ) (w : Fin n → R)
    (hv : ∀ j : Fin n, (v j.val : ℂ) = φ (w j)) (chart : Fin (n + 1)) :
    FiniteBad (p.map φ) v chart ↔ ∃ x u : Fin (n + 1) → ℂ, u chart = 1 ∧
      (∀ j, (finiteRows p w j).eval₂ φ x = 0) ∧
        JacobianKernelCharts.matrix φ (finiteRows p w) x *ᵥ u = 0 := by
  rw [finite_bad_map_iff φ p v (fun j => φ (w j)) hv]
  simp only [finiteRows, funext_iff, Fin.forall_fin_succ, JacobianKernelCharts.matrix,
    Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, Fin.cons_zero, Fin.cons_succ,
    map_sub, pderiv_C_mul, eval₂_sub, eval₂_mul, eval₂_C]

theorem real_regular_of_no_bad (p : MvPolynomial (Fin (n + 1)) ℤ) (v : ℕ → ℤ)
    (hgood : ∀ chart, ¬ FiniteBad (p.map (Int.castRingHom ℂ)) v chart)
    (x : Fin (n + 1) → ℝ)
    (hx : ∀ j, (finiteRows p (fun i => v i.val) j).eval₂ (Int.castRingHom ℝ) x = 0) :
    (fderiv ℝ (fun y => fun j => (finiteRows p (fun i => v i.val) j).eval₂ (Int.castRingHom ℝ) y) x).IsInvertible := by
  let rows := finiteRows p (fun i => v i.val)
  let ψ := Int.castRingHom ℂ
  have hcharts : ∀ chart, ¬ ∃ z u : Fin (n + 1) → ℂ, u chart = 1 ∧
      (∀ j, (rows j).eval₂ ψ z = 0) ∧ JacobianKernelCharts.matrix ψ rows z *ᵥ u = 0 := by
    intro chart hb
    exact hgood chart ((finite_bad_iff_kernel ψ p v (fun i => v i.val) (fun _ => rfl) chart).mpr hb)
  have hregular := (JacobianKernelCharts.regular_iff_charts ψ rows).mpr hcharts
  have hmap : Complex.ofRealHom.comp (Int.castRingHom ℝ) = ψ := RingHom.ext_int _ _
  have he (q : MvPolynomial (Fin (n + 1)) ℤ) :
      q.eval₂ ψ (Complex.ofRealHom ∘ x) = Complex.ofRealHom (q.eval₂ (Int.castRingHom ℝ) x) := by
    rw [← hmap, ← eval₂_comp_left]
  have hz (j) : (rows j).eval₂ ψ (fun i => (x i : ℂ)) = 0 := by
    change (rows j).eval₂ ψ (Complex.ofRealHom ∘ x) = 0
    rw [he, hx j, map_zero]
  have hd := hregular (fun i => (x i : ℂ)) hz
  apply (PolynomialSystemRegularity.isInvertible_iff (Int.castRingHom ℝ) rows x).mpr
  intro hzero
  apply hd
  change (JacobianKernelCharts.jacobian rows).eval₂ ψ (Complex.ofRealHom ∘ x) = 0
  rw [he, JacobianKernelCharts.eval_jacobian]
  change Complex.ofRealHom (PolynomialSystemRegularity.matrix (Int.castRingHom ℝ) rows x).det = 0
  rw [hzero, map_zero]

end LeanCanny.ETR.ComplexCircuit.CriticalKernel
