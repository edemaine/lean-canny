/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCurrentQSelectedCoordinate
/-! # Coordinate cut choices and roots persist after an actual retained command -/
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

theorem coefficient_scaling (i : ℕ) :
    ((coordinate (step x hm c) hn (shiftRule x hm c r) j).coeff i).map ψ.toRingHom=
      C (coordinateScale x hm c r)*((coordinate x hm r j).coeff i).map φ.toRingHom :=by
  simpa only [selected,Polynomial.coeff_map,Polynomial.coeff_C_mul,Polynomial.coe_mapRingHom] using
    congrArg (fun p : Polynomial (Polynomial ℝ)=>p.coeff i)
      (selected_scaling x hm c hn r hr φ ψ values a H HN j)

theorem coordinate_valid_iff (i : Fin (IntegralMixedCoordinateTrailing.ChoiceBound P r)) :
    IntegralMixedCoordinateTrailing.Valid (step x hm c) hn (shiftRule x hm c r) j ψ i ↔
      IntegralMixedCoordinateTrailing.Valid x hm r j φ i :=by
  have HS : C (coordinateScale x hm c r) ≠ (0:Polynomial ℝ):=
    Polynomial.C_ne_zero.mpr (coordinateScale_ne_zero x hm c r)
  unfold IntegralMixedCoordinateTrailing.Valid
  simp only [coefficient_scaling x hm c hn r hr φ ψ values a H HN j,mul_eq_zero,HS,false_or]
  constructor
  · rintro ⟨HL,HT⟩
    exact ⟨HL,(mul_ne_zero_iff.mp HT).2⟩
  · rintro ⟨HL,HT⟩
    exact ⟨HL,mul_ne_zero HS HT⟩

theorem coordinate_factor_scaling (i : Fin (IntegralMixedCoordinateTrailing.ChoiceBound P r)) :
    (IntegralMixedCoordinateTrailing.factor (step x hm c) hn (shiftRule x hm c r) j i).map ψ.toRingHom=
      C (coordinateScale x hm c r)*(IntegralMixedCoordinateTrailing.factor x hm r j i).map φ.toRingHom :=
  coefficient_scaling x hm c hn r hr φ ψ values a H HN j i.val

theorem coordinate_factor_degree (i : Fin (IntegralMixedCoordinateTrailing.ChoiceBound P r)) :
    ((IntegralMixedCoordinateTrailing.factor (step x hm c) hn (shiftRule x hm c r) j i).map ψ.toRingHom).natDegree=
      ((IntegralMixedCoordinateTrailing.factor x hm r j i).map φ.toRingHom).natDegree :=by
  rw [coordinate_factor_scaling x hm c hn r hr φ ψ values a H HN j]
  exact Polynomial.natDegree_C_mul (coordinateScale_ne_zero x hm c r)

theorem coordinate_factor_root_iff (i : Fin (IntegralMixedCoordinateTrailing.ChoiceBound P r)) (t : ℝ) :
    (IntegralMixedCoordinateTrailing.factor (step x hm c) hn (shiftRule x hm c r) j i).eval₂ ψ.toRingHom t=0 ↔
      (IntegralMixedCoordinateTrailing.factor x hm r j i).eval₂ φ.toRingHom t=0 :=by
  rw [←Polynomial.eval_map,←Polynomial.eval_map,
    coordinate_factor_scaling x hm c hn r hr φ ψ values a H HN j]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,mul_eq_zero,
    coordinateScale_ne_zero x hm c r,false_or]

end LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
