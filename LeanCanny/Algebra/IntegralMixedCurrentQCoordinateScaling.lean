/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCommandClearing
public import LeanCanny.Algebra.IntegralMixedCriticalSweep
public import LeanCanny.Algebra.ClearedCriticalCommonScaling
/-! # Actual current-Q sweep data after a retained command

The old quotient values, not a supplied polynomial covariance, determine
the selected heights. Successive Q values differ by the actual producing
leading. This module tracks the resulting common frozen clearing factor.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
open IntegralMixedHistory IntegralMixedFullHistoryScript IntegralMixedCriticalSweep Polynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem denominator_scale {N : ℕ} (scales : Fin N→ℤ) (L : ℤ) :
    CommonIntegerDenominator.denominator Finset.univ (fun i=>L*scales i)=
      L^N*CommonIntegerDenominator.denominator Finset.univ scales :=by
  simp only [CommonIntegerDenominator.denominator,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]

theorem numerator_scale {R : Type*} [CommRing R] (scales : Fin (n+1)→ℤ)
    (H : Fin (n+1)→R) (L : ℤ) (i : Fin (n+1)) :
    CommonIntegerDenominator.numerator Finset.univ (fun j=>L*scales j) (fun j=>(L:R)*H j) i=
      (L:R)^(n+1)*CommonIntegerDenominator.numerator Finset.univ scales H i :=by
  have HC : ((Finset.univ : Finset (Fin (n+1))).erase i).card=n:=by simp
  simp only [CommonIntegerDenominator.numerator,CommonIntegerDenominator.denominator,
    Finset.prod_mul_distrib,Finset.prod_const,HC,Int.cast_mul,Int.cast_pow]
  rw [pow_succ]
  ring

noncomputable def shiftRule (x : State P S B m ι) (hm : m≤S) (c : Command P B) (r : Rule n) : Rule n where
  critical:={r.critical with heights:=fun i=>LeanCanny.Geometry.IntegralMixedFrozenFrame.later (r.critical.heights i)}
  height:=r.height
  height_frozen:=r.height_frozen
  slope:=commonDenominator (step x hm c)
  slope_ne_zero:=commonDenominator_ne_zero _

theorem scales (x : State P S B m ι) (hm : m≤S) (c : Command P B) (hn : m+1≤S)
    (r : Rule n) (i : Fin (n+1)) :
    (data (step x hm c) hn (shiftRule x hm c r).critical).scales i=
      leading x hm c*(data x hm r.critical).scales i :=by
  change commonDenominator (step x hm c)*r.critical.scales i=
    leading x hm c*(commonDenominator x*r.critical.scales i)
  rw [command_commonDenominator]
  ring

theorem selected_heights (x : State P S B m ι) (hm : m≤S) (c : Command P B) (r : Rule n)
    (hr : r.slope=commonDenominator x)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : (step x hm c).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (a : ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (HN : ∀ i,ψ ((step x hm c).bank.numerator i)/((step x hm c).bank.denominator i:ℝ)=
      (Fin.cons a values : Fin (m+1)→ℝ) i)
    (i : Fin (n+1)) :
    (heights (step x hm c) (shiftRule x hm c r) i).map ψ.toRingHom=
      C (leading x hm c:ℝ)*(heights x r i).map φ.toRingHom :=by
  unfold heights shiftRule
  simp only [Polynomial.map_add,Polynomial.map_C]
  have HE : ψ.toRingHom (expression (step x hm c)
      (LeanCanny.Geometry.IntegralMixedFrozenFrame.later (r.critical.heights i)))=
      (leading x hm c:ℝ)*φ.toRingHom (expression x (r.critical.heights i)):=
    command_expression_later x hm c φ ψ values a H HN _
  rw [HE]
  by_cases hi : i=r.height
  · simp only [hi,ite_true,Polynomial.map_mul,Polynomial.map_X,Polynomial.map_intCast,
      map_intCast,hr,command_commonDenominator,Int.cast_mul,Polynomial.C_mul]
    ring
  · simp only [hi,ite_false,Polynomial.map_zero,add_zero,Polynomial.C_mul]

theorem denominator (x : State P S B m ι) (hm : m≤S) (c : Command P B) (hn : m+1≤S) (r : Rule n) :
    CoordinateFrozenCriticalElimination.denominator (data (step x hm c) hn (shiftRule x hm c r).critical).scales=
      (leading x hm c)^(n+1)*CoordinateFrozenCriticalElimination.denominator (data x hm r.critical).scales :=by
  have HS : (data (step x hm c) hn (shiftRule x hm c r).critical).scales=
      fun i=>leading x hm c*(data x hm r.critical).scales i:=by
    funext i
    exact scales x hm c hn r i
  rw [HS]
  exact denominator_scale _ _

end LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
