/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ParameterizedBoundaryCriticalValues
public import LeanCanny.Algebra.CriticalValueSystem
public import LeanCanny.Geometry.ParametricFiniteCoordinateGram
/-! # Fixed Gram slices for the actual regularized norm-boundary values

The source is the sum of squares of the actual Lagrangian critical-value
equations. Its value coordinate has finite image at every real parameter,
derived from the ambient polynomial critical-value theorem. The same fixed
Gram deformation slice consequently annihilates every actual boundary value
outside its explicit nonzero coefficient exception.
-/
@[expose] public section
namespace LeanCanny.Geometry.ParameterizedBoundaryGramValues
open LeanCanny.Algebra MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

noncomputable def lagrangian (q : MvPolynomial (Fin n) ℤ) :
    MvPolynomial (Fin (n+1)) (Polynomial ℤ) :=
  rename CoerciveCriticalHomogenization.layout (ParameterizedBoundaryCriticalValues.lagrangian q)

noncomputable def energy (q : MvPolynomial (Fin n) ℤ) :
    MvPolynomial (Fin (n+2)) (Polynomial ℤ) :=
  ∑ j : Fin (n+2), (CriticalValueSystem.equations (lagrangian q) j)^2

def degreeBound (D : ℕ) : ℕ := 4*D+6

theorem lagrangian_degree (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D) :
    (lagrangian q).totalDegree ≤ 2*D+3 := by
  have HS : (ParameterizedBoundaryCriticalValues.spatial q).totalDegree ≤ D :=
    (PolynomialMapDegree.degree_le _ _).trans ((totalDegree_rename_le _ _).trans hD)
  have HSub : (ParameterizedBoundaryCriticalValues.spatial q^2 - C Polynomial.X).totalDegree ≤ 2*D :=
    (totalDegree_sub _ _).trans (max_le ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 HS)) (by simp))
  have HMul : (X none * (ParameterizedBoundaryCriticalValues.spatial q^2 - C Polynomial.X)).totalDegree ≤ 1+2*D :=
    (totalDegree_mul _ _).trans (Nat.add_le_add (by simp) HSub)
  apply (totalDegree_rename_le _ _).trans
  apply (totalDegree_add _ _).trans
  apply max_le
  · have HNorm : (∑ i : Fin n, (X (some i) : MvPolynomial (Option (Fin n)) (Polynomial ℤ))^2).totalDegree ≤ 2 :=
      totalDegree_finsetSum_le (fun _ _ => by simp)
    exact HNorm.trans (by omega)
  · exact HMul.trans (by omega)

theorem energy_degree (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D) :
    (energy q).totalDegree ≤ degreeBound D := by
  apply totalDegree_finsetSum_le
  intro j _
  have HL := lagrangian_degree q D hD
  have HR := CriticalValueSystem.degree_le (lagrangian q) (2*D+3) HL (by omega) j
  have HDeg : CriticalValueSystem.degrees (n+1) (2*D+3) j ≤ 2*D+3 := by
    refine Fin.cases (by simp [CriticalValueSystem.degrees])
      (fun i => by simp [CriticalValueSystem.degrees]) j
  exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul_left 2 (HR.trans HDeg)).trans_eq (by
    unfold degreeBound; omega))

theorem energy_zero (q : MvPolynomial (Fin n) ℤ) (φ : Polynomial ℤ →+* ℝ)
    (z : Fin (n+2) → ℝ) : (energy q).eval₂ φ z = 0 ↔
      ∀ j, (CriticalValueSystem.equations (lagrangian q) j).eval₂ φ z = 0 := by
  simp only [energy,eval₂_sum,eval₂_pow,Finset.sum_sq_eq_zero_iff,Finset.mem_univ,forall_const]

theorem finite_values (q : MvPolynomial (Fin n) ℤ) (φ : Polynomial ℤ →+* ℝ) :
    {t : ℝ | ∃ z : Fin (n+2) → ℝ, (energy q).eval₂ φ z = 0 ∧ z 0 = t}.Finite := by
  apply (CriticalValueAnnihilator.finite_critical_values ((lagrangian q).map φ)).subset
  rintro t ⟨z,hz,ht⟩
  have HR := (energy_zero q φ z).mp hz
  have H0 := HR 0
  rw [CriticalValueSystem.eval_equations] at H0
  simp only [Fin.cons_zero,sub_eq_zero] at H0
  refine ⟨fun i => z i.succ,?_,?_⟩
  · intro i
    have H := HR i.succ
    rw [CriticalValueSystem.eval_equations] at H
    simpa only [Fin.cons_succ,pderiv_map,aeval_def,Algebra.algebraMap_self,eval₂_id,eval_map] using H
  · simpa only [aeval_def,Algebra.algebraMap_self,eval₂_id,eval_map] using H0.symm.trans ht

noncomputable def head (q : MvPolynomial (Fin n) ℤ) (D : ℕ) : Polynomial (Polynomial ℤ) :=
  ParametricFiniteCoordinateGram.head (energy q) (degreeBound D) 0

noncomputable def exceptional (q : MvPolynomial (Fin n) ℤ) (D : ℕ) : Polynomial ℤ :=
  ParametricFiniteCoordinateGram.exceptional (energy q) (degreeBound D) 0

theorem head_ne_zero (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D) : head q D ≠ 0 :=
  ParametricFiniteCoordinateGram.head_ne_zero (energy q) (degreeBound D) (energy_degree q D hD) 0

theorem exceptional_ne_zero (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D) : exceptional q D ≠ 0 :=
  ParametricFiniteCoordinateGram.exceptional_ne_zero (energy q) (degreeBound D) (energy_degree q D hD) 0

theorem eval_head (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (e : ℝ) (hexc : ParameterizedBoundaryCriticalValues.parameter e (exceptional q D) ≠ 0)
    (x : Fin n → ℝ) (lambda : ℝ) (he : (q.eval₂ (Int.castRingHom ℝ) x)^2 = e)
    (hx : ∀ i, 2*x i + lambda*(2*q.eval₂ (Int.castRingHom ℝ) x*
      (pderiv i q).eval₂ (Int.castRingHom ℝ) x) = 0) :
    (head q D).eval₂ (ParameterizedBoundaryCriticalValues.parameter e) (∑ i, x i^2) = 0 := by
  let φ := ParameterizedBoundaryCriticalValues.parameter e
  let old : Option (Fin n) → ℝ := fun j => j.elim lambda x
  let y : Fin (n+1) → ℝ := fun j => old (CoerciveCriticalHomogenization.layout.symm j)
  have HY : y ∘ CoerciveCriticalHomogenization.layout = old := by
    funext j
    simp only [y,Function.comp_apply,Equiv.symm_apply_apply]
  have HL : (lagrangian q).eval₂ φ y = ∑ i, x i^2 := by
    rw [lagrangian,eval₂_rename,HY,ParameterizedBoundaryCriticalValues.lagrangian_eval,
      he,sub_self,mul_zero,add_zero]
  have HG : ∀ j, (pderiv j (lagrangian q)).eval₂ φ y = 0 := by
    intro j
    have HD := pderiv_rename CoerciveCriticalHomogenization.layout.injective
      (CoerciveCriticalHomogenization.layout.symm j) (ParameterizedBoundaryCriticalValues.lagrangian q)
    simp only [Equiv.apply_symm_apply] at HD
    rw [lagrangian,HD,eval₂_rename,HY]
    exact ParameterizedBoundaryCriticalValues.lagrangian_critical q e x lambda he hx _
  let z : Fin (n+2) → ℝ := Fin.cons (∑ i, x i^2) y
  have HZ : (energy q).eval₂ φ z = 0 := by
    apply (energy_zero q φ z).mpr
    intro j
    have H := CriticalValueSystem.critical_root φ (lagrangian q) y HG j
    rwa [HL] at H
  have HF : {t : ℝ | ∃ z : Fin (n+2) → ℝ, ((energy q).map φ).eval z = 0 ∧ z 0 = t}.Finite := by
    simpa only [MvPolynomial.eval_map] using finite_values q φ
  have H := ParametricFiniteCoordinateGram.eval_head (energy q) (degreeBound D)
    (energy_degree q D hD) 0 φ hexc HF z (by simpa only [MvPolynomial.eval_map] using HZ)
  exact H

end LeanCanny.Geometry.ParameterizedBoundaryGramValues
