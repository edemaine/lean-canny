/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CubeCoordinates
public import LeanCanny.Algebra.RationalSubstitution
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Polynomial equations on compact inner cubes

Canny's rational coordinate change is cleared by an even denominator power for
each variable. The resulting integer polynomial preserves zeros and signs on
the open cube. A real zero exists exactly when one of its compact inner-cube
zero sets is nonempty; smaller positive margins preserve nonemptiness.
-/

@[expose] public section

namespace LeanCanny.Geometry.CubePolynomial
open MvPolynomial
open scoped BigOperators
open CubeCoordinates

variable {ι : Type*} [Fintype ι]

noncomputable def cleared (p : MvPolynomial ι ℤ) : MvPolynomial ι ℤ :=
  ∑ e ∈ p.support, C (p.coeff e) * ∏ i, X i ^ e i * (1 - X i ^ 2) ^ (2 * p.degreeOf i - e i)

noncomputable def scale (p : MvPolynomial ι ℤ) (y : ι → ℝ) : ℝ :=
  ∏ i, (1 - y i ^ 2) ^ (2 * p.degreeOf i)

theorem eval_cleared (p : MvPolynomial ι ℤ) (y : ι → ℝ) (hy : OpenCube y) :
    (cleared p).eval₂ (Int.castRingHom ℝ) y = scale p y * p.eval₂ (Int.castRingHom ℝ) (coordinates y) := by
  classical
  let psi := MvPolynomial.eval₂Hom (Int.castRingHom ℝ) y
  have hC (z : ℤ) : psi (C z) = (z : ℝ) := MvPolynomial.eval₂_C _ _ _
  have hX (i : ι) : psi (X i) = y i := MvPolynomial.eval₂_X _ _ _
  change psi (cleared p) = _
  simp only [cleared, map_sum, map_mul, map_prod, map_pow, map_sub, map_one, hC, hX]
  rw [MvPolynomial.eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  change (p.coeff e : ℝ) * ∏ i, y i ^ e i * (1 - y i ^ 2) ^ (2 * p.degreeOf i - e i) = _
  calc
    _ = (p.coeff e : ℝ) * ∏ i, (1 - y i ^ 2) ^ (2 * p.degreeOf i) * (y i / (1 - y i ^ 2)) ^ e i := by
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact (LeanCanny.Algebra.RationalSubstitution.scale_div_pow _ _ _ _
        ((MvPolynomial.monomial_le_degreeOf i he).trans (by omega)) (ne_of_gt (one_sub_sq_pos (y i) (hy i)))).symm
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [scale, coordinates, toLine, Int.coe_castRingHom]
      ring

theorem scale_pos (p : MvPolynomial ι ℤ) (y : ι → ℝ) (hy : OpenCube y) : 0 < scale p y := by
  classical
  exact Finset.prod_pos fun i _ => pow_pos (one_sub_sq_pos (y i) (hy i)) _

theorem zero_iff (p : MvPolynomial ι ℤ) (y : ι → ℝ) (hy : OpenCube y) :
    (cleared p).eval₂ (Int.castRingHom ℝ) y = 0 ↔ p.eval₂ (Int.castRingHom ℝ) (coordinates y) = 0 := by
  rw [eval_cleared p y hy]
  exact mul_eq_zero.trans (or_iff_right (ne_of_gt (scale_pos p y hy)))

theorem sign_eq (p : MvPolynomial ι ℤ) (y : ι → ℝ) (hy : OpenCube y) :
    SignType.sign ((cleared p).eval₂ (Int.castRingHom ℝ) y) =
      SignType.sign (p.eval₂ (Int.castRingHom ℝ) (coordinates y)) := by
  rw [eval_cleared p y hy, sign_mul, sign_pos (scale_pos p y hy), one_mul]

theorem totalDegree_le (p : MvPolynomial ι ℤ) : (cleared p).totalDegree ≤ 4 * ∑ i, p.degreeOf i := by
  classical
  unfold cleared
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e he
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, Nat.zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hden : (1 - (X i : MvPolynomial ι ℤ) ^ 2).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  have hp1 : ((X i : MvPolynomial ι ℤ) ^ e i).totalDegree ≤ e i := by
    simp only [MvPolynomial.totalDegree_X_pow, le_refl]
  have hp2 := (MvPolynomial.totalDegree_pow (1 - (X i : MvPolynomial ι ℤ) ^ 2)
    (2 * p.degreeOf i - e i)).trans (Nat.mul_le_mul_left _ hden)
  have hpow := MvPolynomial.monomial_le_degreeOf i he
  exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)

theorem totalDegree_le_card (p : MvPolynomial ι ℤ) :
    (cleared p).totalDegree ≤ 4 * Fintype.card ι * p.totalDegree := by
  apply (totalDegree_le p).trans
  have h : (∑ i, p.degreeOf i) ≤ Fintype.card ι * p.totalDegree := by
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => MvPolynomial.degreeOf_le_totalDegree p i)
  exact (Nat.mul_le_mul_left 4 h).trans_eq (Nat.mul_assoc _ _ _).symm

omit [Fintype ι] in
theorem continuous_eval (p : MvPolynomial ι ℤ) : Continuous fun y : ι → ℝ => p.eval₂ (Int.castRingHom ℝ) y := by
  simpa only [MvPolynomial.eval_map] using MvPolynomial.continuous_eval (p.map (Int.castRingHom ℝ))

def zeroSet (p : MvPolynomial ι ℤ) (epsilon : ℝ) : Set (ι → ℝ) :=
  closedCube ι epsilon ∩ {y | (cleared p).eval₂ (Int.castRingHom ℝ) y = 0}

theorem isCompact_zeroSet (p : MvPolynomial ι ℤ) (epsilon : ℝ) : IsCompact (zeroSet p epsilon) :=
  (isCompact_closedCube ι epsilon).inter_right (isClosed_eq (continuous_eval (cleared p)) continuous_const)

theorem exists_zero_iff_nonempty (p : MvPolynomial ι ℤ) :
    (∃ x : ι → ℝ, p.eval₂ (Int.castRingHom ℝ) x = 0) ↔
      ∃ epsilon : ℝ, 0 < epsilon ∧ (zeroSet p epsilon).Nonempty := by
  rw [exists_iff_openCube]
  constructor
  · rintro ⟨y, hy, hp⟩
    obtain ⟨epsilon, he, hm⟩ := (openCube_iff_exists_margin y).mp hy
    exact ⟨epsilon, he, y, hm, (zero_iff p y hy).mpr hp⟩
  · rintro ⟨epsilon, he, y, hm, hp⟩
    have hy := (openCube_iff_exists_margin y).mpr ⟨epsilon, he, hm⟩
    exact ⟨y, hy, (zero_iff p y hy).mp hp⟩

theorem zeroSet_mono (p : MvPolynomial ι ℤ) {epsilon eta : ℝ} (h : eta ≤ epsilon) :
    zeroSet p epsilon ⊆ zeroSet p eta := fun _ hy => ⟨closedCube_mono h hy.1, hy.2⟩

theorem exists_linear_max (p : MvPolynomial ι ℤ) (epsilon : ℝ) (h : (zeroSet p epsilon).Nonempty) (v : ι → ℝ) :
    ∃ y ∈ zeroSet p epsilon, ∀ z ∈ zeroSet p epsilon, (∑ i, v i * z i) ≤ ∑ i, v i * y i := by
  have hc : Continuous (fun y : ι → ℝ => ∑ i, v i * y i) :=
    continuous_finsetSum Finset.univ (fun i _ => continuous_const.mul (continuous_apply i))
  exact (isCompact_zeroSet p epsilon).exists_isMaxOn h hc.continuousOn

end LeanCanny.Geometry.CubePolynomial
