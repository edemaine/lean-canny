/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialFormalCenter
public import LeanCanny.Connectivity.FormulaSignSlotRadialParameterEliminant
public import LeanCanny.Algebra.IntegralParameterInverseSpecialization
/-! # Exact formal-center eliminants and guarded specialized coordinate extraction -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialFormalEliminant
open ETR LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Algebra
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def eliminant (c :List Bool) (i :Fin (N c+d c+1)):
    Polynomial (Polynomial (FormulaSignSlotRadialFormalCenter.Radius c)):=
  ParametricTiltedCoerciveEliminant.polynomial (FormulaSignSlotRadialFormalCenter.polynomial c)
    (degreeBudget c) (marginIndex c) i

theorem specialization (c :List Bool) (a :Fin (d c)→ℝ) (i :Fin (N c+d c+1)):
    ParametricTiltedCoerciveEliminant.coefficientMap (FormulaSignSlotRadialFormalCenter.radiusMap c a)
      (eliminant c i)=FormulaSignSlotRadialParameterEliminant.eliminant c a i:=by
  unfold eliminant FormulaSignSlotRadialParameterEliminant.eliminant
  rw [ParametricTiltedCoerciveEliminant.polynomial_map,FormulaSignSlotRadialFormalCenter.polynomial_specialization]

theorem coefficient_specialization (c :List Bool) (a :Fin (d c)→ℝ) (i :Fin (N c+d c+1)) (τ :ℕ):
    (FormulaSignSlotRadialParameterEliminant.eliminant c a i).coeff τ=
      ((eliminant c i).coeff τ).map (FormulaSignSlotRadialFormalCenter.radiusMap c a):=by
  have H:=congrArg (fun p :Polynomial (Polynomial (Polynomial ℝ))=>p.coeff τ) (specialization c a i)
  simpa only [ParametricTiltedCoerciveEliminant.coefficientMap,Polynomial.coe_mapRingHom,Polynomial.coeff_map] using H.symm

/-- The stored perturbation index is checked AFTER specializing the center.
All lower coefficient polynomials must vanish and this coefficient must survive. -/
theorem natTrailingDegree_at (c :List Bool) (a :Fin (d c)→ℝ) (i :Fin (N c+d c+1)) (τ :ℕ)
    (Hbelow:∀k<τ,((eliminant c i).coeff k).map (FormulaSignSlotRadialFormalCenter.radiusMap c a)=0)
    (Hτ:((eliminant c i).coeff τ).map (FormulaSignSlotRadialFormalCenter.radiusMap c a)≠0):
    (FormulaSignSlotRadialParameterEliminant.eliminant c a i).natTrailingDegree=τ:=by
  have H:=IntegralParameterInverse.natTrailingDegree_map_at
    (R:=Polynomial (FormulaSignSlotRadialFormalCenter.Radius c)) (S:=Polynomial (Polynomial ℝ))
    (Polynomial.mapRingHom (FormulaSignSlotRadialFormalCenter.radiusMap c a)) (eliminant c i) τ Hbelow Hτ
  change (ParametricTiltedCoerciveEliminant.coefficientMap
    (FormulaSignSlotRadialFormalCenter.radiusMap c a) (eliminant c i)).natTrailingDegree=τ at H
  rw [specialization] at H
  exact H

theorem coordinate_at (c :List Bool) (a :Fin (d c)→ℝ) (i :Fin (N c+d c+1)) (τ :ℕ)
    (Hbelow:∀k<τ,((eliminant c i).coeff k).map (FormulaSignSlotRadialFormalCenter.radiusMap c a)=0)
    (Hτ:((eliminant c i).coeff τ).map (FormulaSignSlotRadialFormalCenter.radiusMap c a)≠0):
    FormulaSignSlotRadialParameterEliminant.coordinate c a i=
      ((eliminant c i).coeff τ).map (FormulaSignSlotRadialFormalCenter.radiusMap c a):=by
  change (FormulaSignSlotRadialParameterEliminant.eliminant c a i).coeff
    (FormulaSignSlotRadialParameterEliminant.eliminant c a i).natTrailingDegree=_
  rw [natTrailingDegree_at c a i τ Hbelow Hτ]
  exact coefficient_specialization c a i τ

/-- A suitable index exists for every actual center, even when specialization
kills the symbolic lowest coefficient. Its bound here is algebraic natDegree;
no native degree reader or eliminant mass bound is asserted. -/
theorem exists_coordinate_index (c :List Bool) (a :Fin (d c)→ℝ) (i :Fin (N c+d c+1)):
    ∃τ≤(eliminant c i).natDegree,
      (∀k<τ,((eliminant c i).coeff k).map (FormulaSignSlotRadialFormalCenter.radiusMap c a)=0) ∧
      ((eliminant c i).coeff τ).map (FormulaSignSlotRadialFormalCenter.radiusMap c a)≠0 ∧
      FormulaSignSlotRadialParameterEliminant.coordinate c a i=
        ((eliminant c i).coeff τ).map (FormulaSignSlotRadialFormalCenter.radiusMap c a):=by
  let τ:=(FormulaSignSlotRadialParameterEliminant.eliminant c a i).natTrailingDegree
  have HP:=FormulaSignSlotRadialParameterEliminant.eliminant_ne_zero c a i
  have Hbelow:∀k<τ,((eliminant c i).coeff k).map (FormulaSignSlotRadialFormalCenter.radiusMap c a)=0:=by
    intro k hk
    rw [←coefficient_specialization]
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hk
  have Hτ:((eliminant c i).coeff τ).map (FormulaSignSlotRadialFormalCenter.radiusMap c a)≠0:=by
    rw [←coefficient_specialization]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr HP
  have HF:(eliminant c i).coeff τ≠0:=by
    intro HZ
    exact Hτ (by rw [HZ,Polynomial.map_zero])
  exact ⟨τ,Polynomial.le_natDegree_of_ne_zero HF,Hbelow,Hτ,coordinate_at c a i τ Hbelow Hτ⟩

end LeanCanny.Connectivity.FormulaSignSlotRadialFormalEliminant
