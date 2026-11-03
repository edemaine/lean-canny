/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCurrentQPrincipalScaling
/-! # Squarefree exceptional cut roots persist after an actual retained command -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
open IntegralMixedHistory IntegralMixedFullHistoryScript IntegralMixedCriticalSweep Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable (x : State P S B m ι) (hm : m≤S) (c : Command P B) (hn : m+1≤S)
    (r : Rule n) (hr : r.slope=commonDenominator x)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : (step x hm c).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (a : ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (HN : ∀ i,ψ ((step x hm c).bank.numerator i)/((step x hm c).bank.denominator i:ℝ)=
      (Fin.cons a values : Fin (m+1)→ℝ) i)
    (j : Fin (n-r.critical.offset.val+1))
include hr H HN


noncomputable def squarefreeScale (k : ℕ) : ℝ :=
  coordinateScale x hm c r*principalScale x hm c r k

omit [Fintype ι] hr H HN in
theorem squarefreeScale_ne_zero (k : ℕ) : squarefreeScale x hm c r k ≠ 0 :=
  mul_ne_zero (coordinateScale_ne_zero x hm c r) (principalScale_ne_zero x hm c r k)

theorem squarefree_factor_scaling (k : Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r)) :
    (IntegralMixedCoordinateSquarefree.exceptional (step x hm c) hn (shiftRule x hm c r) j k).map ψ.toRingHom=
      C (squarefreeScale x hm c r k.val)*(IntegralMixedCoordinateSquarefree.exceptional x hm r j k).map φ.toRingHom :=by
  unfold IntegralMixedCoordinateSquarefree.exceptional
  rw [Polynomial.map_mul,Polynomial.map_mul,
    coefficient_scaling x hm c hn r hr φ ψ values a H HN j,
    principal_scaling x hm c hn r hr φ ψ values a H HN j]
  rw [squarefreeScale,map_mul]
  dsimp only [IntegralMixedCoordinateSquarefree.coordinateDegree,shiftRule]
  ring

theorem squarefree_factor_degree (k : Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r)) :
    ((IntegralMixedCoordinateSquarefree.exceptional (step x hm c) hn (shiftRule x hm c r) j k).map ψ.toRingHom).natDegree=
      ((IntegralMixedCoordinateSquarefree.exceptional x hm r j k).map φ.toRingHom).natDegree :=by
  rw [squarefree_factor_scaling x hm c hn r hr φ ψ values a H HN j]
  exact Polynomial.natDegree_C_mul (squarefreeScale_ne_zero x hm c r k.val)

theorem squarefree_factor_root_iff (k : Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r)) (t : ℝ) :
    (IntegralMixedCoordinateSquarefree.exceptional (step x hm c) hn (shiftRule x hm c r) j k).eval₂ ψ.toRingHom t=0 ↔
      (IntegralMixedCoordinateSquarefree.exceptional x hm r j k).eval₂ φ.toRingHom t=0 :=by
  rw [←Polynomial.eval_map,←Polynomial.eval_map,
    squarefree_factor_scaling x hm c hn r hr φ ψ values a H HN j]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,mul_eq_zero,
    squarefreeScale_ne_zero x hm c r k.val,false_or]

end LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
