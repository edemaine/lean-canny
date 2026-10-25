/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MvCoefficientMass
public import LeanCanny.Algebra.CoefficientMass
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Integer polynomial representation of one retained parameter

The parameter becomes variable zero, followed by the spatial variables.
Evaluation agrees with successive parameter and spatial evaluation. Separate
degree and coefficient-mass bounds give bounds for this integer polynomial.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegerParameterFlatten
open scoped Classical BigOperators
open MvPolynomial
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def coefficientMap : Polynomial R →+* MvPolynomial (Fin (n + 1)) R :=
  Polynomial.eval₂RingHom C (X 0)

noncomputable def flatten : MvPolynomial (Fin n) (Polynomial R) →+* MvPolynomial (Fin (n + 1)) R :=
  eval₂Hom coefficientMap (fun i => X i.succ)

@[simp] theorem flatten_X (i : Fin n) : flatten (X i : MvPolynomial (Fin n) (Polynomial R)) = X i.succ :=
  eval₂Hom_X' _ _ _

@[simp] theorem flatten_C (p : Polynomial R) :
    flatten (C p : MvPolynomial (Fin n) (Polynomial R)) = coefficientMap p :=
  eval₂Hom_C _ _ _

theorem eval_coefficientMap {S : Type*} [CommRing S] (φ : R →+* S)
    (p : Polynomial R) (z : Fin (n + 1) → S) :
    (coefficientMap p).eval₂ φ z = p.eval₂ φ (z 0) := by
  have h : (eval₂Hom φ z).comp coefficientMap = Polynomial.eval₂RingHom φ (z 0) := by
    ext <;> simp [coefficientMap]
  exact congrArg (fun f : Polynomial R →+* S => f p) h

theorem eval_flatten {S : Type*} [CommRing S] (φ : R →+* S)
    (q : MvPolynomial (Fin n) (Polynomial R)) (z : Fin (n + 1) → S) :
    (flatten q).eval₂ φ z = q.eval₂ (Polynomial.eval₂RingHom φ (z 0)) (fun i => z i.succ) := by
  induction q using MvPolynomial.induction_on with
  | C c => simpa only [flatten, eval₂Hom_C, eval₂_C, Polynomial.coe_eval₂RingHom] using
      eval_coefficientMap φ c z
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | mul_X p i hp => simp only [flatten, map_mul, eval₂Hom_X', eval₂_mul, eval₂_X] at hp ⊢; rw [hp]

theorem pderiv_coefficientMap (p : Polynomial R) (i : Fin n) :
    pderiv i.succ (coefficientMap p) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | monomial k a => simp [coefficientMap, Polynomial.eval₂_monomial]

theorem flatten_pderiv (q : MvPolynomial (Fin n) (Polynomial R)) (i : Fin n) :
    flatten (pderiv i q) = pderiv i.succ (flatten q) := by
  induction q using MvPolynomial.induction_on with
  | C c => simp only [pderiv_C, map_zero, flatten_C, pderiv_coefficientMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    have hX : flatten (pderiv i (X j : MvPolynomial (Fin n) (Polynomial R))) =
        pderiv i.succ (X j.succ : MvPolynomial (Fin (n + 1)) R) := by
      by_cases hij : j = i <;> simp [pderiv_X, hij, flatten]
    simp only [pderiv_mul, map_add, map_mul, hp, hX, flatten_X]

theorem flatten_det_pderiv (q : Fin n → MvPolynomial (Fin n) (Polynomial R)) :
    flatten (Matrix.det (fun i j => pderiv j (q i))) =
      Matrix.det (fun i j => pderiv j.succ (flatten (q i))) := by
  rw [flatten.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  exact flatten_pderiv _ _

theorem coefficientMap_degree [Nontrivial R] (p : Polynomial R) :
    (coefficientMap (n := n) p).totalDegree ≤ p.natDegree := by
  change (p.eval₂ C (X 0 : MvPolynomial (Fin (n + 1)) R)).totalDegree ≤ p.natDegree
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum]
  apply totalDegree_finsetSum_le
  intro k hk
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, Nat.zero_add]
  exact (totalDegree_pow _ _).trans (by
    rw [totalDegree_X, Nat.mul_one]
    exact Polynomial.le_natDegree_of_mem_supp k hk)

theorem flatten_degree [Nontrivial R] (q : MvPolynomial (Fin n) (Polynomial R)) (D E : ℕ)
    (hD : q.totalDegree ≤ D) (hE : ∀ e, (q.coeff e).natDegree ≤ E) :
    (flatten q).totalDegree ≤ E + D := by
  change (q.eval₂ coefficientMap (fun i => X i.succ)).totalDegree ≤ E + D
  rw [MvPolynomial.eval₂_eq]
  apply totalDegree_finsetSum_le
  intro e he
  apply (totalDegree_mul _ _).trans
  apply Nat.add_le_add ((coefficientMap_degree _).trans (hE e))
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ i ∈ e.support, e i := Finset.sum_le_sum fun i _ =>
      (totalDegree_pow _ _).trans (by rw [totalDegree_X, Nat.mul_one])
    _ ≤ D := (MvPolynomial.le_totalDegree he).trans hD

theorem coefficientMap_mass (p : Polynomial ℤ) :
    MvMass.mass (coefficientMap (n := n) p) ≤ coefficientMass p := by
  change MvMass.mass (p.eval₂ C (X 0 : MvPolynomial (Fin (n + 1)) ℤ)) ≤ coefficientMass p
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum, coefficientMass, Polynomial.sum]
  apply (MvMass.sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  apply (MvMass.mul_le _ _).trans
  simpa only [MvMass.C, MvMass.X, one_pow, Nat.mul_one] using
    Nat.mul_le_mul_left (p.coeff k).natAbs (MvMass.pow_le (X 0 : MvPolynomial (Fin (n + 1)) ℤ) k)

theorem flatten_mass (q : MvPolynomial (Fin n) (Polynomial ℤ)) (b : ℕ)
    (hb : ∀ e, coefficientMass (q.coeff e) ≤ 2 ^ b) :
    MvMass.mass (flatten q) ≤ q.support.card * 2 ^ b := by
  change MvMass.mass (q.eval₂ coefficientMap (fun i => X i.succ)) ≤ _
  rw [MvPolynomial.eval₂_eq]
  apply (MvMass.sum_le _ _).trans
  calc
    _ ≤ ∑ _e ∈ q.support, 2 ^ b := by
      apply Finset.sum_le_sum
      intro e _
      apply (MvMass.mul_le _ _).trans
      have hp : MvMass.mass (∏ i ∈ e.support, (X i.succ : MvPolynomial (Fin (n + 1)) ℤ) ^ e i) ≤ 1 := by
        apply (MvMass.prod_le _ _).trans
        simpa only [MvMass.X, one_pow, Finset.prod_const_one] using
          Finset.prod_le_prod (fun i (_ : i ∈ e.support) =>
            MvMass.pow_le (X i.succ : MvPolynomial (Fin (n + 1)) ℤ) (e i))
      exact (Nat.mul_le_mul ((coefficientMap_mass _).trans (hb e)) hp).trans_eq (Nat.mul_one _)
    _ = _ := by simp

theorem support_card (q : MvPolynomial (Fin n) (Polynomial R)) (D : ℕ)
    (hD : q.totalDegree ≤ D) : q.support.card ≤ (D + 1) ^ n := by
  let f : q.support → (Fin n → Fin (D + 1)) := fun e i =>
    ⟨e.val i, ((monomial_le_degreeOf i e.property).trans
      ((degreeOf_le_totalDegree q i).trans hD)).trans_lt (Nat.lt_succ_self D)⟩
  have hf : Function.Injective f := by
    intro e g he
    apply Subtype.ext
    ext i
    exact congrArg Fin.val (congrFun he i)
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_le_of_injective f hf

def massExponent (n D b : ℕ) : ℕ := n * (D + 1).size + b

theorem flatten_mass_pow (q : MvPolynomial (Fin n) (Polynomial ℤ)) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hb : ∀ e, coefficientMass (q.coeff e) ≤ 2 ^ b) :
    MvMass.mass (flatten q) ≤ 2 ^ massExponent n D b := by
  calc
    _ ≤ q.support.card * 2 ^ b := flatten_mass q b hb
    _ ≤ (D + 1) ^ n * 2 ^ b := Nat.mul_le_mul_right _ (support_card q D hD)
    _ ≤ (2 ^ (D + 1).size) ^ n * 2 ^ b :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.lt_size_self (D + 1)).le n)
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; unfold massExponent; rw [Nat.mul_comm]

end LeanCanny.Algebra.IntegerParameterFlatten
