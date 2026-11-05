/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValueFamily
public import LeanCanny.Encoding.FormulaSignSlotRadialCoordinatePacket
/-! # The literal coordinate guards select every actual value-system row

All tests use one numerical center. The coordinate varies through the actual
WordList field-zero packet, and every selected perturbation/degree is bounded
by a single original-only bound independent of the coordinate.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterValueSelection
open LeanCanny.Algebra LeanCanny.Connectivity Polynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialFormalEliminant.eliminant

private theorem chosen_degree {R : Type*} [Semiring R] (p : Polynomial R) (tau D : ℕ)
    (f : R → ℕ) : (tau = p.natTrailingDegree ∧ D = f (p.coeff tau)) ↔
      tau = p.natTrailingDegree ∧ D = f p.trailingCoeff := by
  constructor <;> rintro ⟨rfl, H⟩ <;> exact ⟨rfl, H⟩
private theorem guards_at (q c : List Bool) (hc : pairFst q = c) (i : Fin (N c + d c + 1))
    (hi : (FormulaSignSlotRadialEliminantInput.coordinate q).val = i.val) (x : ℕ → ℝ) (tau D : ℕ) :
    FormulaSignSlotRadialCenterSelection.Guards q (fun j => x j.val) tau D ↔
      tau = (FormulaSignSlotRadialParameterEliminant.eliminant c (fun j => x j.val) i).natTrailingDegree ∧
      D = (FormulaSignSlotRadialParameterEliminant.coordinate c (fun j => x j.val) i).natDegree := by
  rw [FormulaSignSlotRadialCenterSelection.guards_iff, chosen_degree]
  cases hc
  have HI : FormulaSignSlotRadialEliminantInput.coordinate q = i := Fin.ext hi
  unfold FormulaSignSlotRadialCenterSelection.specialized
  rw [HI]
  rfl

theorem coordinate_guards (c : List Bool) (i : Fin (N c + d c + 1)) (x : ℕ → ℝ) (tau D : ℕ) :
    FormulaSignSlotRadialCenterSelection.Guards (FormulaSignSlotRadialCoordinatePacket.packet c i.val)
      (fun j => x j.val) tau D ↔
      tau = (FormulaSignSlotRadialParameterEliminant.eliminant c (fun j => x j.val) i).natTrailingDegree ∧
      D = (FormulaSignSlotRadialParameterEliminant.coordinate c (fun j => x j.val) i).natDegree := by
  apply guards_at _ c (FormulaSignSlotRadialCoordinatePacket.root c i.val) i
  rw [FormulaSignSlotRadialCoordinatePacket.selected, Nat.min_eq_left (by omega)]

theorem all_guards (c : List Bool) (x : ℕ → ℝ) (tau D : Fin (N c + d c + 1) → ℕ) :
    (∀ i, FormulaSignSlotRadialCenterSelection.Guards (FormulaSignSlotRadialCoordinatePacket.packet c i.val)
      (fun j => x j.val) (tau i) (D i)) ↔
        FormulaSignSlotRadialCenterValueFamily.Guards c (fun j => x j.val) tau D := by
  apply forall_congr'
  intro i
  exact coordinate_guards c i x (tau i) (D i)

noncomputable def bound (c : List Bool) :=
  FormulaSignSlotRadialEliminantPacked.resultDegree (FormulaSignSlotRadialCoordinatePacket.packet c 0)
theorem bound_eq (c : List Bool) (i : ℕ) :
    FormulaSignSlotRadialCenterSelection.bound (FormulaSignSlotRadialCoordinatePacket.packet c i) = bound c := by
  simp only [FormulaSignSlotRadialCenterSelection.bound, bound, FormulaSignSlotRadialEliminantPacked.resultDegree,
    FormulaSignSlotRadialEliminantPackingLayout.columns, FormulaSignSlotRadialEliminantPackingLayout.width,
    FormulaSignSlotRadialEliminantPackingLayout.spatial, FormulaSignSlotRadialEliminantPackingLayout.sourceDegree,
    FormulaSignSlotRadialEliminantPackingLayout.parameterDegree, FormulaSignSlotRadialCoordinatePacket.root]

theorem exists_bounded_guards (c : List Bool) (x : ℕ → ℝ) :
    ∃ tau D : Fin (N c + d c + 1) → ℕ,
      (∀ i, tau i ≤ bound c ∧ D i ≤ bound c) ∧
        FormulaSignSlotRadialCenterValueFamily.Guards c (fun j => x j.val) tau D := by
  have HE (i : Fin (N c + d c + 1)) := FormulaSignSlotRadialCenterSelection.exists_guards
    (FormulaSignSlotRadialCoordinatePacket.packet c i.val) (fun j => x j.val)
  simp_rw [bound_eq] at HE
  choose tau ht D hD HG using HE
  exact ⟨tau, D, fun i => ⟨ht i, hD i⟩, (all_guards c x tau D).mp HG⟩

end LeanCanny.Encoding.FormulaSignSlotRadialCenterValueSelection
