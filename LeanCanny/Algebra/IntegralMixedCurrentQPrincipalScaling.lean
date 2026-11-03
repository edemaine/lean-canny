/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCurrentQCoordinateCuts
public import LeanCanny.Algebra.IntegralMixedCoordinateSquarefree
/-! # Actual principal subresultants under retained current-Q scaling -/
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
theorem selected_principal (k : ℕ) :
    (IntegralMixedCoordinateSquarefree.principal x hm r j k).map φ.toRingHom=
      PrincipalSubresultant.psc (selected x hm r j φ) (selected x hm r j φ).derivative
        (IntegralMixedCoordinateSquarefree.coordinateDegree P r)
        (IntegralMixedCoordinateSquarefree.coordinateDegree P r-1) k :=by
  unfold IntegralMixedCoordinateSquarefree.principal selected
  change (Polynomial.mapRingHom φ.toRingHom) _ = _
  rw [Polynomial.derivative_map,PrincipalSubresultant.psc_map_map]

noncomputable def principalScale (k : ℕ) : ℝ :=
  coordinateScale x hm c r^((IntegralMixedCoordinateSquarefree.coordinateDegree P r-1-k)+
    (IntegralMixedCoordinateSquarefree.coordinateDegree P r-k))

omit [Fintype ι] in
theorem principalScale_ne_zero (k : ℕ) : principalScale x hm c r k ≠ 0 :=
  pow_ne_zero _ (coordinateScale_ne_zero x hm c r)

include hr H HN

theorem principal_scaling (k : ℕ) :
    (IntegralMixedCoordinateSquarefree.principal (step x hm c) hn (shiftRule x hm c r) j k).map ψ.toRingHom=
      C (principalScale x hm c r k)*(IntegralMixedCoordinateSquarefree.principal x hm r j k).map φ.toRingHom :=by
  rw [selected_principal,selected_principal,selected_scaling x hm c hn r hr φ ψ values a H HN j,
    Polynomial.derivative_C_mul,PrincipalSubresultant.psc_C_mul_left,PrincipalSubresultant.psc_C_mul_right]
  dsimp only [principalScale,IntegralMixedCoordinateSquarefree.coordinateDegree,shiftRule]
  rw [←mul_assoc,←map_pow,←map_pow,←map_mul,←pow_add]

theorem squarefree_valid_iff (k : Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r)) :
    IntegralMixedCoordinateSquarefree.Valid (step x hm c) hn (shiftRule x hm c r) j ψ k ↔
      IntegralMixedCoordinateSquarefree.Valid x hm r j φ k :=by
  have HS (i : ℕ) : C (principalScale x hm c r i) ≠ (0:Polynomial ℝ):=
    Polynomial.C_ne_zero.mpr (principalScale_ne_zero x hm c r i)
  unfold IntegralMixedCoordinateSquarefree.Valid
  simp only [principal_scaling x hm c hn r hr φ ψ values a H HN j,mul_eq_zero,HS,false_or]
  constructor
  · rintro ⟨HL,HT⟩
    exact ⟨HL,(mul_ne_zero_iff.mp HT).2⟩
  · rintro ⟨HL,HT⟩
    exact ⟨HL,mul_ne_zero (HS _) HT⟩

end LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
