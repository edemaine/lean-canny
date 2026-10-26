/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FermatCriticalDirection
public import LeanCanny.ETR.ComplexCriticalKernelFinite
public import LeanCanny.Algebra.JacobianKernelCharts

/-! # Bounded direction records with empty critical-kernel charts

The bounded integer direction theorem controls the actual spatial Jacobian.
Its nonsingularity excludes every normalized kernel chart used by the shared
Hessian circuits, over the complex numbers.
-/

@[expose] public section
namespace LeanCanny.Encoding.FermatCriticalDirection
open MvPolynomial LeanCanny.Algebra LeanCanny.ETR.ComplexCircuit
open scoped Classical BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem finite_bad_iff_parameter_kernel (low : MvPolynomial (Fin (n + 1)) ℚ) (a : ℚ)
    (N : ℕ) (v : ℕ → ℤ) (w : Fin n → ℕ)
    (hv : ∀ j : Fin n, v j.val = (w j : ℤ)) (chart : Fin (n + 1)) :
    let ψ := eval₂Hom (algebraMap ℚ ℂ) (fun i => (w i : ℂ))
    CriticalKernel.FiniteBad ((FermatCriticalHomogenization.polynomial low a N).map (algebraMap ℚ ℂ)) v chart ↔
      ∃ x u : Fin (n + 1) → ℂ, u chart = 1 ∧
        (∀ j, (FermatCriticalBadSystem.equations low a N j).eval₂ ψ x = 0) ∧
          JacobianKernelCharts.matrix ψ (FermatCriticalBadSystem.equations low a N) x *ᵥ u = 0 := by
  dsimp only
  have hv' (j : Fin n) : (v j.val : ℂ) = (w j : ℂ) := by
    rw [hv j, Int.cast_natCast]
  rw [CriticalKernel.finite_bad_map_iff (algebraMap ℚ ℂ) _ v (fun j => (w j : ℂ)) hv']
  simp only [FermatCriticalBadSystem.equations, FermatCriticalHomogenization.spatial,
    funext_iff, Fin.forall_fin_succ, JacobianKernelCharts.matrix, Matrix.mulVec, dotProduct,
    Matrix.of_apply, Pi.zero_apply, Fin.cons_zero, Fin.cons_succ, map_sub, pderiv_C_mul,
    eval₂_sub, eval₂_mul, eval₂_C, eval₂Hom_X', ← FermatCriticalHomogenization.map_polynomial,
    pderiv_map, eval₂_map, eval₂Hom_comp_C]

theorem exists_record_no_bad (low : MvPolynomial (Fin (n + 1)) ℚ) (a : ℚ) (ha : a ≠ 0)
    (N : ℕ) (hlow : low.totalDegree < N) (hN : 1 < N)
    (hregular : ∀ (L : Type) [Field L] [Algebra ℚ L] (x : Fin (n + 1) → L),
      aeval x (FermatCriticalHomogenization.polynomial low a N) = 0 →
        ∃ j, aeval x (pderiv j (FermatCriticalHomogenization.polynomial low a N)) ≠ 0) :
    ∃ record : List Bool, record.length = n * FermatBoundedCriticalDirection.binaryWidth n N ∧
      ∀ chart : Fin (n + 1), ¬ CriticalKernel.FiniteBad
        ((FermatCriticalHomogenization.polynomial low a N).map (algebraMap ℚ ℂ))
        (fun i => (FixedWidthQuery.coordinate (fun _ => FermatBoundedCriticalDirection.binaryWidth n N) id record i : ℤ)) chart := by
  obtain ⟨r, hr, hgood⟩ := exists_record low a ha N hlow hN hregular
  refine ⟨r, hr, ?_⟩
  let ψ := eval₂Hom (algebraMap ℚ ℂ) (fun i => (assignment n N r i : ℂ))
  have hcharts := (JacobianKernelCharts.regular_iff_charts ψ (FermatCriticalBadSystem.equations low a N)).mp
    (hgood ℂ)
  intro chart
  exact fun hb => hcharts chart ((finite_bad_iff_parameter_kernel low a N _ (assignment n N r)
    (fun _ => rfl) chart).mp hb)

end LeanCanny.Encoding.FermatCriticalDirection
