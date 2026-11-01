/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialValueCertificate
public import LeanCanny.Geometry.RealParameterRootBranches
public import LeanCanny.Geometry.AlgebraicBranchSign
/-! # Constructed finite cuts for actual positive radial branches

The cuts combine the actual perturbation-limit coordinates, their squarefree
preprocessing, the actual slice-value Gram certificate and the margin's lowest
coefficient. An existing radial sample proves the value certificate nonzero;
no branch regularity, properness or row-pruning hypothesis is supplied.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialBranchCuts
open ETR Set Polynomial LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Algebra
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits FormulaSignSlotRadialParameterEliminant
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialParameterPolynomial.polynomial degreeBudget
  FormulaSignSlotMargin.initialDimension FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialPolynomial

noncomputable def cuts (c : List Bool) (a : Fin (d c) → ℝ) : Set ℝ :=
  bad c a ∪ RealParameterRootBranches.bad (coordinate c a) ∪
    {r | (FormulaSignSlotRadialValueCertificate.polynomial c a).trailingCoeff.eval r=0} ∪
    {r | (coordinate c a (marginIndex c)).trailingCoeff.eval r=0}

theorem finite_cuts (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (hr : r∉bad c a)
    (x : Fin (N c+d c+1) → ℝ) (hx : x∈FormulaSignSlotRadialParameterGrid.grid c a r) : (cuts c a).Finite :=
  (((finite_bad c a).union (RealParameterRootBranches.finite_bad _ (coordinate_ne_zero c a))).union
    (FormulaSignSlotRadialValueCertificate.finite_cuts c a r hr x hx)).union
      (AlgebraicBranchZero.finite_exceptional _ (coordinate_ne_zero c a (marginIndex c)))

theorem conditions (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (h : r∉cuts c a) :
    r∉bad c a ∧ r∉RealParameterRootBranches.bad (coordinate c a) ∧
    (FormulaSignSlotRadialValueCertificate.polynomial c a).trailingCoeff.eval r≠0 ∧
    (coordinate c a (marginIndex c)).trailingCoeff.eval r≠0 := by
  simpa only [cuts,mem_union,mem_ofPred_eq,not_or,and_assoc] using h

theorem small_interval (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (hr : r∉bad c a)
    (x : Fin (N c+d c+1) → ℝ) (hx : x∈FormulaSignSlotRadialParameterGrid.grid c a r) :
    ∃ b : ℝ, 0 < b ∧ ∀ t∈Ioo 0 b, t∉cuts c a := by
  obtain ⟨l,b,hl,hb,HI⟩ := CoerciveConstrainedSampling.exists_isolating_interval (cuts c a) (finite_cuts c a r hr x hx) 0
  refine ⟨b,hb,?_⟩
  intro t ht hbad
  exact (ne_of_gt ht.1) (HI t hbad ⟨hl.le.trans ht.1.le,ht.2.le⟩)

noncomputable def system (c : List Bool) (a : Fin (d c) → ℝ) := RealParameterRootBranches.system (coordinate c a)

theorem branches (c : List Bool) (a : Fin (d c) → ℝ) (b : ℝ) (t₀ : Ioo (0 : ℝ) b)
    (h : ∀ t∈Ioo 0 b, t∉cuts c a) :
    Finite (RootBranches.Index (system c a) 0 b t₀) ∧
    ∃ curve : RootBranches.Index (system c a) 0 b t₀ → C(Ioo (0 : ℝ) b, Fin (N c+d c+1) → ℝ),
      (∀ i, curve i t₀=i.val.val.val.2) ∧
      (∀ i t, curve i t∈FormulaSignSlotRadialParameterGrid.grid c a t.val) ∧
      ∀ t : Ioo (0 : ℝ) b, ∀ x, x∈FormulaSignSlotRadialParameterGrid.grid c a t.val ↔ ∃! i, curve i t=x := by
  have HA : ∀ t∈Ioo 0 b, t∉RealParameterRootBranches.bad (coordinate c a) := fun t ht => (conditions c a t (h t ht)).2.1
  exact ⟨RealParameterRootBranches.finite_index _ 0 b t₀ HA,RealParameterRootBranches.branches _ 0 b t₀ HA⟩
end LeanCanny.Connectivity.FormulaSignSlotRadialBranchCuts
