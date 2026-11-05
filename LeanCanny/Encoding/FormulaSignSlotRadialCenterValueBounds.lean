/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValueSelection
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValueLayout
public import LeanCanny.Algebra.RelativeAffineGridValueParameterDegree
public import LeanCanny.Algebra.NestedTotalDegree
public import LeanCanny.Algebra.MvTwoParameterCoefficient
/-! # One joint radius/center box for the actual radial value certificate -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterValueBounds
open LeanCanny.Algebra LeanCanny.Connectivity Polynomial MvPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialFormalEliminant.eliminant

private theorem degree_at (q c : List Bool) (hc : pairFst q = c)
    (i : Fin (N c + d c + 1)) (hi : (FormulaSignSlotRadialEliminantInput.coordinate q).val = i.val) :
    (FormulaSignSlotRadialEliminantParameterRows.eliminant c i).totalDegree ≤
      FormulaSignSlotRadialEliminantPacked.resultDegree q := by
  cases hc
  have HI : FormulaSignSlotRadialEliminantInput.coordinate q = i := Fin.ext hi
  rw [← HI]
  exact FormulaSignSlotRadialEliminantPacked.result_degree q

theorem eliminant_degree (c : List Bool) (i : Fin (N c + d c + 1)) :
    (FormulaSignSlotRadialEliminantParameterRows.eliminant c i).totalDegree ≤
      FormulaSignSlotRadialCenterValueSelection.bound c := by
  have H := degree_at (FormulaSignSlotRadialCoordinatePacket.packet c i.val) c
    (FormulaSignSlotRadialCoordinatePacket.root c i.val) i
    (by rw [FormulaSignSlotRadialCoordinatePacket.selected, Nat.min_eq_left (by omega)])
  exact H.trans_eq (FormulaSignSlotRadialCenterValueSelection.bound_eq c i.val)

private theorem one_one {A : ℕ} (p : Polynomial (MvPolynomial (Fin A) ℤ)) (k : ℕ) :
    MvTwoParameterCoefficient.one (TriplePolynomialParameterFlatten.one p) k = p.coeff k := by
  unfold MvTwoParameterCoefficient.one TriplePolynomialParameterFlatten.one
  change ((MvPolynomial.finSuccEquiv ℤ A) ((MvPolynomial.finSuccEquiv ℤ A).symm p)).coeff k = _
  rw [AlgEquiv.apply_symm_apply]
private theorem slice_flatten {A : ℕ} (p : Polynomial (Polynomial (Polynomial (MvPolynomial (Fin A) ℤ))))
    (s t : ℕ) : MvTwoParameterCoefficient.slice (TriplePolynomialParameterFlatten.flatten p) s t =
      TriplePolynomialParameterFlatten.one ((p.coeff s).coeff t) := by
  unfold MvTwoParameterCoefficient.slice TriplePolynomialParameterFlatten.flatten
  rw [RingHom.comp_apply, one_one]
  simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  unfold TriplePolynomialParameterFlatten.two
  rw [RingHom.comp_apply, one_one]
  simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]

theorem input_degree (c : List Bool) (tau D : Fin (N c + d c + 1) → ℕ)
    (i : Fin (N c + d c + 1)) (j : ℕ) :
    (TriplePolynomialParameterFlatten.one ((FormulaSignSlotRadialCenterValueFamily.input c tau D i).coeff j)).totalDegree ≤
      FormulaSignSlotRadialCenterValueSelection.bound c := by
  rw [FormulaSignSlotRadialCenterValueFamily.input,
    FormulaSignSlotRadialCenterSquarefreeSelection.truncate_coefficient]
  split_ifs
  · rw [← slice_flatten]
    exact (MvTwoParameterCoefficient.degree _ _ _).trans (eliminant_degree c i)
  · simp

private theorem constant_bound {m A : ℕ} (p : MvPolynomial (Fin A) ℤ) (D : ℕ) (h : p.totalDegree ≤ D) :
    NestedTotalDegree.Bound (MvPolynomial.C p : MvPolynomial (Fin m) (MvPolynomial (Fin A) ℤ)) D := by
  intro e
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact h
  · simp
private theorem spatial_bound {m A : ℕ} (i : Fin m) :
    NestedTotalDegree.Bound (MvPolynomial.X i : MvPolynomial (Fin m) (MvPolynomial (Fin A) ℤ)) 1 := by
  intro e
  rw [MvPolynomial.coeff_X]
  split_ifs <;> simp
private theorem square_bound {m A : ℕ} (i : Fin m) (p : MvPolynomial (Fin A) ℤ) (h : p.totalDegree ≤ 1) :
    NestedTotalDegree.Bound ((MvPolynomial.X i - MvPolynomial.C p)^2) 2 := by
  have H := NestedTotalDegree.sub (spatial_bound i) (constant_bound p 1 h)
  simpa only [pow_two] using NestedTotalDegree.mul H H

theorem test_degree (c : List Bool) (v : Fin (N c + d c + 1) →₀ ℕ) :
    (TriplePolynomialParameterFlatten.one ((FormulaSignSlotRadialFormalCenter.polynomial c).coeff v)).totalDegree ≤ 2 := by
  have HC : TriplePolynomialParameterFlatten.one.comp (FormulaSignSlotRadialFormalCenter.constants c) =
      (MvPolynomial.C : ℤ →+* MvPolynomial (Fin (d c + 1)) ℤ) := Subsingleton.elim _ _
  have HBase : NestedTotalDegree.Bound
      ((((FormulaSignSlotCenteredRadialSource.equation c).finitePolynomial (N c + d c + 1)).map
        (MvPolynomial.C : ℤ →+* MvPolynomial (Fin (d c + 1)) ℤ))) 2 := by
    intro e
    simp only [MvPolynomial.coeff_map, MvPolynomial.totalDegree_C, Nat.zero_le]
  have HCenter (i : Fin (d c)) :
      (TriplePolynomialParameterFlatten.one (Polynomial.C (MvPolynomial.X i : MvPolynomial (Fin (d c)) ℤ))).totalDegree ≤ 1 := by
    have HE : TriplePolynomialParameterFlatten.one (Polynomial.C (MvPolynomial.X i : MvPolynomial (Fin (d c)) ℤ)) = MvPolynomial.X i.succ := by
      apply (MvPolynomial.finSuccEquiv ℤ (d c)).injective
      change (MvPolynomial.finSuccEquiv ℤ (d c))
        ((MvPolynomial.finSuccEquiv ℤ (d c)).symm (Polynomial.C (MvPolynomial.X i))) = _
      rw [AlgEquiv.apply_symm_apply, MvPolynomial.finSuccEquiv_X_succ]
    rw [HE]
    simp
  have HRadius : (TriplePolynomialParameterFlatten.one (Polynomial.X : Polynomial (MvPolynomial (Fin (d c)) ℤ))).totalDegree ≤ 1 := by
    have HE : TriplePolynomialParameterFlatten.one (Polynomial.X : Polynomial (MvPolynomial (Fin (d c)) ℤ)) = MvPolynomial.X 0 := by
      apply (MvPolynomial.finSuccEquiv ℤ (d c)).injective
      change (MvPolynomial.finSuccEquiv ℤ (d c))
        ((MvPolynomial.finSuccEquiv ℤ (d c)).symm Polynomial.X) = _
      rw [AlgEquiv.apply_symm_apply, MvPolynomial.finSuccEquiv_X_zero]
    rw [HE]
    simp
  have H := NestedTotalDegree.add (NestedTotalDegree.add HBase
    (NestedTotalDegree.sum Finset.univ (fun i =>
      (MvPolynomial.X (FormulaSignSlotCenteredRadialGraph.centerIndex c i) - MvPolynomial.C
        (TriplePolynomialParameterFlatten.one (Polynomial.C (MvPolynomial.X i : MvPolynomial (Fin (d c)) ℤ))))^2)
      2 (fun i _ => square_bound _ _ (HCenter i))))
    (square_bound (FormulaSignSlotCenteredRadialGraph.radiusIndex c) _ HRadius)
  have HE : (FormulaSignSlotRadialFormalCenter.polynomial c).map TriplePolynomialParameterFlatten.one =
      (((FormulaSignSlotCenteredRadialSource.equation c).finitePolynomial (N c + d c + 1)).map
        (MvPolynomial.C : ℤ →+* MvPolynomial (Fin (d c + 1)) ℤ)) +
      (∑ i : Fin (d c), (MvPolynomial.X (FormulaSignSlotCenteredRadialGraph.centerIndex c i) -
        MvPolynomial.C (TriplePolynomialParameterFlatten.one (Polynomial.C (MvPolynomial.X i : MvPolynomial (Fin (d c)) ℤ))))^2) +
      (MvPolynomial.X (FormulaSignSlotCenteredRadialGraph.radiusIndex c) -
        MvPolynomial.C (TriplePolynomialParameterFlatten.one (Polynomial.X : Polynomial (MvPolynomial (Fin (d c)) ℤ))))^2 := by
    unfold FormulaSignSlotRadialFormalCenter.polynomial
    simp only [map_add, map_pow, map_sub, map_sum, MvPolynomial.map_X, MvPolynomial.map_C, MvPolynomial.map_map, HC]
  rw [← HE] at H
  simpa only [MvPolynomial.coeff_map] using H v

theorem polynomial_degree (c : List Bool) (tau D : Fin (N c + d c + 1) → ℕ) (j : ℕ) :
    (TriplePolynomialParameterFlatten.one ((FormulaSignSlotRadialCenterValueFamily.polynomial c tau D).coeff j)).totalDegree ≤
      RelativeProjectiveValueGram.dimension (N c + d c + 1)
        (RelativeAffineGridValueGram.width D (FormulaSignSlotCenteredRadialLimits.degreeBudget c + 1)) *
          (FormulaSignSlotRadialCenterValueSelection.bound c + 2) :=
  RelativeAffineGridValueParameterDegree.degree _ _ _ _ _
    (fun i k => (input_degree c tau D i k).trans (Nat.le_add_right _ 2))
    (fun v => (test_degree c v).trans (by omega)) j

end LeanCanny.Encoding.FormulaSignSlotRadialCenterValueBounds
