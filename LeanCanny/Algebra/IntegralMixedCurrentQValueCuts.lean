/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCurrentQSelectedRows
public import LeanCanny.Algebra.IntegralMixedCurrentQSelectedCoordinate
public import LeanCanny.Algebra.RelativeAffineGridValueMap
public import LeanCanny.Algebra.RelativeAffineGridValueScaling
public import LeanCanny.Algebra.IntegralMixedValueTrailing
/-! # Value-Gram cut choices and roots persist after an actual retained command -/
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



omit [Fintype ι] in
theorem selected_value_eq :
    IntegralMixedValueTrailing.selectedValue x hm r j φ=
      RelativeAffineGridValueGram.annihilator (fun i=>selected x hm r i φ)
        ((IntegralMixedSweepRows.row x hm r j).map (Polynomial.mapRingHom φ.toRingHom))
        (fun _=>IntegralMixedCoordinateSquarefree.coordinateDegree P r) P.degree :=by
  exact RelativeAffineGridValueMap.annihilator φ.toRingHom _ _ _ _

omit [Fintype ι] in
theorem selected_value_gram_nonzero :
    RelativeProjectiveValueGram.polynomial
      (AffineRingCoordinates.homogeneousRows (RelativeAffineGridValueGram.rows (fun i=>selected x hm r i φ))
        (fun _=>IntegralMixedCoordinateSquarefree.coordinateDegree P r))
      (RelativeAffineGridValueGram.test ((IntegralMixedSweepRows.row x hm r j).map (Polynomial.mapRingHom φ.toRingHom)) P.degree)
      (fun _=>IntegralMixedCoordinateSquarefree.coordinateDegree P r) P.degree
      (RelativeAffineGridValueGram.width (fun _ : Fin (n-r.critical.offset.val+1)=>IntegralMixedCoordinateSquarefree.coordinateDegree P r) P.degree)≠0 :=by
  have HP:=IntegralMixedGridValue.selected_ne_zero x hm r j φ
  change IntegralMixedValueTrailing.selectedValue x hm r j φ≠0 at HP
  rw [selected_value_eq] at HP
  unfold RelativeAffineGridValueGram.annihilator RelativeProjectiveValueGram.annihilator at HP
  intro HZ
  exact HP (by rw [HZ,Polynomial.reflect_zero,mul_zero])

include hr H HN

theorem selected_value_trailing_degree :
    (IntegralMixedValueTrailing.selectedValue (step x hm c) hn (shiftRule x hm c r) j ψ).natTrailingDegree=
      (IntegralMixedValueTrailing.selectedValue x hm r j φ).natTrailingDegree :=by
  rw [selected_value_eq,selected_value_eq]
  have HC : (fun i=>selected (step x hm c) hn (shiftRule x hm c r) i ψ)=
      fun i=>C (C (coordinateScale x hm c r))*selected x hm r i φ:=by
    funext i
    exact selected_scaling x hm c hn r hr φ ψ values a H HN i
  rw [HC,selected_row_scaling x hm c hn r hr φ ψ values a H HN j]
  exact RelativeAffineGridValueScaling.trailing_degree_scale _ _ _ _
    (coordinateScale x hm c r) (rowScale x hm c) (coordinateScale_ne_zero x hm c r)
    (rowScale_ne_zero x hm c) (selected_value_gram_nonzero x hm r φ j)

theorem value_valid_iff (k : Fin (IntegralMixedValueTrailing.ChoiceBound P r)) :
    IntegralMixedValueTrailing.Valid (step x hm c) hn (shiftRule x hm c r) j ψ k ↔
      IntegralMixedValueTrailing.Valid x hm r j φ k :=by
  rw [IntegralMixedValueTrailing.valid_iff,IntegralMixedValueTrailing.valid_iff,
    selected_value_trailing_degree x hm c hn r hr φ ψ values a H HN j]

theorem selected_value_trailing_zero (t : ℝ) :
    (IntegralMixedValueTrailing.selectedValue (step x hm c) hn (shiftRule x hm c r) j ψ).trailingCoeff.eval t=0 ↔
      (IntegralMixedValueTrailing.selectedValue x hm r j φ).trailingCoeff.eval t=0 :=by
  rw [selected_value_eq,selected_value_eq]
  have HC : (fun i=>selected (step x hm c) hn (shiftRule x hm c r) i ψ)=
      fun i=>C (C (coordinateScale x hm c r))*selected x hm r i φ:=by
    funext i
    exact selected_scaling x hm c hn r hr φ ψ values a H HN i
  rw [HC,selected_row_scaling x hm c hn r hr φ ψ values a H HN j]
  exact RelativeAffineGridValueScaling.trailing_zero_scale _ _ _ _
    (coordinateScale x hm c r) (rowScale x hm c) (coordinateScale_ne_zero x hm c r)
    (rowScale_ne_zero x hm c) (selected_value_gram_nonzero x hm r φ j) t

theorem value_factor_root_iff (k : Fin (IntegralMixedValueTrailing.ChoiceBound P r))
    (hk : IntegralMixedValueTrailing.Valid x hm r j φ k) (t : ℝ) :
    (IntegralMixedValueTrailing.factor (step x hm c) hn (shiftRule x hm c r) j k).eval₂ ψ.toRingHom t=0 ↔
      (IntegralMixedValueTrailing.factor x hm r j k).eval₂ φ.toRingHom t=0 :=by
  have HNvalid:=(value_valid_iff x hm c hn r hr φ ψ values a H HN j k).mpr hk
  rw [←Polynomial.eval_map,←Polynomial.eval_map,
    IntegralMixedValueTrailing.factor_specialization _ _ _ _ _ _ HNvalid,
    IntegralMixedValueTrailing.factor_specialization _ _ _ _ _ _ hk]
  exact selected_value_trailing_zero x hm c hn r hr φ ψ values a H HN j t

end LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
