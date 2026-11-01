/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialParameterGrid
public import LeanCanny.Algebra.RelativeAffineGridValueGram
public import LeanCanny.Geometry.AlgebraicBranchZero
/-! # A constructed value certificate prunes the actual radial coordinate grid

The reciprocal Gram certificate is built from the uniform radius equations and
the literal frozen slice polynomial. Repeated roots are allowed. A single
nonexceptional grid sample proves every coordinate degree positive and hence
nonvanishing of this actual certificate. Its trailing coefficient makes the
slice equation zero status constant on continuous grid branches.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialValueCertificate
open ETR Set Polynomial LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Algebra
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits FormulaSignSlotRadialParameterEliminant
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialParameterPolynomial.polynomial degreeBudget
  FormulaSignSlotMargin.initialDimension FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialPolynomial

noncomputable def polynomial (c : List Bool) (a : Fin (d c) → ℝ) : Polynomial (Polynomial ℝ) :=
  RelativeAffineGridValueGram.annihilator (coordinate c a) (FormulaSignSlotRadialParameterPolynomial.polynomial c a)
    (fun i => (coordinate c a i).natDegree) (degreeBudget c+1)

theorem root (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (x : Fin (N c+d c+1) → ℝ)
    (hx : x∈FormulaSignSlotRadialParameterGrid.grid c a r) :
    (polynomial c a).eval₂ (Polynomial.evalRingHom r)
      ((FormulaSignSlotCenteredRadialLimits.polynomial c a r).eval x)=0 := by
  have H := RelativeAffineGridValueGram.root (coordinate c a) (FormulaSignSlotRadialParameterPolynomial.polynomial c a)
    (fun i => (coordinate c a i).natDegree) (degreeBudget c+1) (fun _ => le_rfl)
    ((FormulaSignSlotRadialParameterPolynomial.degree c a).trans (Nat.le_succ _)) (Polynomial.evalRingHom r) x hx
  change (polynomial c a).eval₂ (Polynomial.evalRingHom r) _=0 at H
  rw [← FormulaSignSlotRadialParameterPolynomial.specialization c a r,MvPolynomial.eval_map]
  exact H

theorem coordinate_positive (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ)
    (hr : r∉bad c a) (x : Fin (N c+d c+1) → ℝ) (hx : x∈FormulaSignSlotRadialParameterGrid.grid c a r)
    (i : Fin (N c+d c+1)) : 0 < (coordinate c a i).natDegree := by
  have HP := mapped_coordinate_ne_zero c a r hr i
  have HD : 0 < ((coordinate c a i).map (Polynomial.evalRingHom r)).natDegree := by
    by_contra H
    have HE := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos H)
    have Hroot : ((coordinate c a i).map (Polynomial.evalRingHom r)).eval (x i)=0 := by
      rw [Polynomial.eval_map]
      exact hx i
    rw [HE,Polynomial.eval_C] at Hroot
    exact HP (by rw [HE,Hroot,Polynomial.C_0])
  exact HD.trans_le Polynomial.natDegree_map_le

theorem ne_zero (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (hr : r∉bad c a)
    (x : Fin (N c+d c+1) → ℝ) (hx : x∈FormulaSignSlotRadialParameterGrid.grid c a r) : polynomial c a≠0 := by
  have H := RelativeAffineGridValueGram.selected_ne_zero (coordinate c a)
    (FormulaSignSlotRadialParameterPolynomial.polynomial c a) (fun i => (coordinate c a i).natDegree)
    (degreeBudget c+1) (fun _ => rfl) (coordinate_positive c a r hr x hx) (Nat.succ_pos _)
    (RingHom.id ℝ) r (fun i => ?_)
  · change (polynomial c a).map (Polynomial.mapRingHom (RingHom.id ℝ))≠0 at H
    intro HZ
    exact H (by rw [HZ,Polynomial.map_zero])
  · change Complex.ofReal ((coordinate c a i).leadingCoeff.eval₂ (RingHom.id ℝ) r)≠0
    rw [Polynomial.eval₂_id]
    exact fun HZ => hr ⟨i,Complex.ofReal_eq_zero.mp HZ⟩

theorem finite_cuts (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (hr : r∉bad c a)
    (x : Fin (N c+d c+1) → ℝ) (hx : x∈FormulaSignSlotRadialParameterGrid.grid c a r) :
    {t : ℝ | (polynomial c a).trailingCoeff.eval t=0}.Finite :=
  AlgebraicBranchZero.finite_exceptional _ (ne_zero c a r hr x hx)

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
theorem slice_zero_iff (c : List Bool) (a : Fin (d c) → ℝ)
    (parameter : X → ℝ) (z : X → Fin (N c+d c+1) → ℝ)
    (ht : Continuous parameter) (hz : Continuous z)
    (hgrid : ∀ w, z w∈FormulaSignSlotRadialParameterGrid.grid c a (parameter w))
    (havoid : ∀ w, (polynomial c a).trailingCoeff.eval (parameter w)≠0) (s t : X) :
    (FormulaSignSlotCenteredRadialLimits.polynomial c a (parameter s)).eval (z s)=0 ↔
    (FormulaSignSlotCenteredRadialLimits.polynomial c a (parameter t)).eval (z t)=0 := by
  apply AlgebraicBranchZero.zero_iff (polynomial c a) parameter _ ht _ (fun w => root c a _ _ (hgrid w)) havoid s t
  have H := (PolynomialRootFamily.contDiff_eval (FormulaSignSlotRadialParameterPolynomial.polynomial c a) 1).continuous.comp (ht.prodMk hz)
  convert H using 1
  funext w
  rw [← FormulaSignSlotRadialParameterPolynomial.specialization c a (parameter w),MvPolynomial.eval_map]
  rfl
end LeanCanny.Connectivity.FormulaSignSlotRadialValueCertificate
