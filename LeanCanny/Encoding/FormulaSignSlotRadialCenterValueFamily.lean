/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterSquarefreeSelection
public import LeanCanny.Connectivity.FormulaSignSlotRadialValueCertificate
public import LeanCanny.Algebra.RelativeAffineGridValueMap
/-! # Literal formal-center inputs of the actual radial value certificate

The coordinate equations are selected after specializing the same center.
They remain the original coordinate equations, including repeated factors.
The tested row is the literal formal radial source polynomial.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterValueFamily
open LeanCanny.Algebra LeanCanny.Connectivity Polynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialFormalEliminant.eliminant
  FormulaSignSlotRadialFormalCenter.polynomial FormulaSignSlotRadialParameterPolynomial.polynomial

noncomputable def input (c : List Bool) (tau D : Fin (N c + d c + 1) → ℕ)
    (i : Fin (N c + d c + 1)) : Polynomial (FormulaSignSlotRadialFormalCenter.Radius c) :=
  FormulaSignSlotRadialCenterSquarefreeSelection.truncate
    ((FormulaSignSlotRadialFormalEliminant.eliminant c i).coeff (tau i)) (D i)
noncomputable def polynomial (c : List Bool) (tau D : Fin (N c + d c + 1) → ℕ) :=
  RelativeAffineGridValueGram.annihilator (input c tau D)
    (FormulaSignSlotRadialFormalCenter.polynomial c) D (degreeBudget c + 1)
noncomputable def Guards (c : List Bool) (a : Fin (d c) → ℝ)
    (tau D : Fin (N c + d c + 1) → ℕ) : Prop :=
  ∀ i, tau i = (FormulaSignSlotRadialParameterEliminant.eliminant c a i).natTrailingDegree ∧
    D i = (FormulaSignSlotRadialParameterEliminant.coordinate c a i).natDegree

private theorem truncate_map {R A : Type*} [Semiring R] [Semiring A] (phi : R →+* A)
    (p : Polynomial R) (D : ℕ) :
    (FormulaSignSlotRadialCenterSquarefreeSelection.truncate p D).map phi =
      FormulaSignSlotRadialCenterSquarefreeSelection.truncate (p.map phi) D := by
  ext j
  rw [Polynomial.coeff_map, FormulaSignSlotRadialCenterSquarefreeSelection.truncate_coefficient,
    FormulaSignSlotRadialCenterSquarefreeSelection.truncate_coefficient, Polynomial.coeff_map]
  split_ifs <;> simp only [map_zero]
private theorem truncate_self {R : Type*} [Semiring R] (p : Polynomial R) (D : ℕ) (h : p.natDegree ≤ D) :
    FormulaSignSlotRadialCenterSquarefreeSelection.truncate p D = p := by
  ext j
  rw [FormulaSignSlotRadialCenterSquarefreeSelection.truncate_coefficient]
  split_ifs with H
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem input_specialization (c : List Bool) (a : Fin (d c) → ℝ)
    (tau D : Fin (N c + d c + 1) → ℕ) (h : Guards c a tau D) (i : Fin (N c + d c + 1)) :
    (input c tau D i).map (FormulaSignSlotRadialFormalCenter.radiusMap c a) =
      FormulaSignSlotRadialParameterEliminant.coordinate c a i := by
  rw [input, truncate_map, ← FormulaSignSlotRadialFormalEliminant.coefficient_specialization]
  have HE : (FormulaSignSlotRadialParameterEliminant.eliminant c a i).coeff (tau i) =
      FormulaSignSlotRadialParameterEliminant.coordinate c a i := by
    rw [(h i).1]
    rfl
  rw [HE]
  exact truncate_self _ _ (by rw [(h i).2])

theorem specialization (c : List Bool) (a : Fin (d c) → ℝ)
    (tau D : Fin (N c + d c + 1) → ℕ) (h : Guards c a tau D) :
    (polynomial c tau D).map (Polynomial.mapRingHom (FormulaSignSlotRadialFormalCenter.centerMap c a)) =
      FormulaSignSlotRadialValueCertificate.polynomial c a := by
  have HI : (fun i => (input c tau D i).map (FormulaSignSlotRadialFormalCenter.radiusMap c a)) =
      FormulaSignSlotRadialParameterEliminant.coordinate c a := funext (input_specialization c a tau D h)
  have HD : D = fun i => (FormulaSignSlotRadialParameterEliminant.coordinate c a i).natDegree :=
    funext (fun i => (h i).2)
  rw [polynomial, RelativeAffineGridValueMap.annihilator]
  change RelativeAffineGridValueGram.annihilator
    (fun i => (input c tau D i).map (FormulaSignSlotRadialFormalCenter.radiusMap c a))
    ((FormulaSignSlotRadialFormalCenter.polynomial c).map (FormulaSignSlotRadialFormalCenter.radiusMap c a)) D _ = _
  rw [HI, FormulaSignSlotRadialFormalCenter.polynomial_specialization, HD]
  rfl

theorem exists_guards (c : List Bool) (a : Fin (d c) → ℝ) :
    ∃ tau D, Guards c a tau D :=
  ⟨fun i => (FormulaSignSlotRadialParameterEliminant.eliminant c a i).natTrailingDegree,
    fun i => (FormulaSignSlotRadialParameterEliminant.coordinate c a i).natDegree, fun _ => ⟨rfl, rfl⟩⟩

end LeanCanny.Encoding.FormulaSignSlotRadialCenterValueFamily
