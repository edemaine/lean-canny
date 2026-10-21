/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Algebra.Polynomial.OfFn
public import LeanCanny.Algebra.CoefficientMass
public import LeanCanny.Algebra.IntegerModular

/-! # A division-free scaled polynomial quotient

The high coefficients of `p*h` form an upper triangular linear system in the
coefficients of `h`. Cramer's determinants recover `coeff(p,d)^(L+1) * h`
without inverting a coefficient. The same formal bounds survive coefficient
maps and modular degree drops.
-/

@[expose] public section

namespace LeanCanny.Algebra.ScaledPolynomialQuotient
open Polynomial Matrix
open scoped BigOperators Classical
variable {R : Type*} [CommRing R]

noncomputable def matrix (p : R[X]) (d L : ℕ) : Matrix (Fin (L + 1)) (Fin (L + 1)) R :=
  fun i j => (p * X ^ j.val).coeff (d + i.val)

theorem matrix_apply (p : R[X]) (d L : ℕ) (i j : Fin (L + 1)) :
    matrix p d L i j = if j.val ≤ d + i.val then p.coeff (d + i.val - j.val) else 0 :=
  coeff_mul_X_pow' p j.val (d + i.val)

theorem matrix_det (p : R[X]) (d L : ℕ) (hp : p.natDegree ≤ d) :
    (matrix p d L).det = p.coeff d ^ (L + 1) := by
  have ht : (matrix p d L).IsUpperTriangular := by
    intro i j hji
    have hji' : j.val < i.val := hji
    rw [matrix_apply, ite_eq_left (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  rw [Matrix.det_of_isUpperTriangular ht]
  have hd (i : Fin (L + 1)) : matrix p d L i i = p.coeff d := by
    rw [matrix_apply, ite_eq_left (by omega), Nat.add_sub_cancel]
  simp only [hd, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

def input (g : R[X]) (d L : ℕ) : Fin (L + 1) → R := fun i => g.coeff (d + i.val)

theorem selected_entry (p g : R[X]) (d L : ℕ) (s i j : Fin (L + 1)) :
    (matrix p d L).updateCol s (input g d L) i j =
      if j = s then g.coeff (d + i.val)
      else if j.val ≤ d + i.val then p.coeff (d + i.val - j.val) else 0 := by
  by_cases h : j = s <;> simp [h, input, matrix_apply]

noncomputable def quotient (p g : R[X]) (d L : ℕ) : R[X] :=
  ofFn (L + 1) (Matrix.cramer (matrix p d L) (input g d L))

theorem quotient_degree (p g : R[X]) (d L : ℕ) : (quotient p g d L).natDegree ≤ L := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  exact ofFn_coeff_eq_zero_of_ge _ (by omega)

theorem quotient_coeff (p g : R[X]) (d L k : ℕ) :
    (quotient p g d L).coeff k =
      if h : k < L + 1 then ((matrix p d L).updateCol ⟨k, h⟩ (input g d L)).det else 0 := by
  by_cases hk : k < L + 1
  · rw [quotient, ofFn_coeff_eq_val_of_lt _ hk, dite_eq_left hk, Matrix.cramer_apply]
  · rw [quotient, ofFn_coeff_eq_zero_of_ge _ (by omega), dite_eq_right hk]

theorem matrix_action (p h : R[X]) (d L : ℕ) (hh : h.natDegree ≤ L) :
    matrix p d L *ᵥ toFn (L + 1) h = input (p * h) d L := by
  have hre : ofFn (L + 1) (toFn (L + 1) h) = h :=
    ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  funext i
  change (∑ j : Fin (L + 1), matrix p d L i j * h.coeff j.val) = (p * h).coeff (d + i.val)
  calc
    _ = (p * ofFn (L + 1) (toFn (L + 1) h)).coeff (d + i.val) := by
      rw [ofFn_eq_sum_monomial, Finset.mul_sum, finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro j _
      rw [show monomial j.val (toFn (L + 1) h j) = C (h.coeff j.val) * X ^ j.val by
        change monomial j.val (h.coeff j.val) = C (h.coeff j.val) * X ^ j.val
        rw [C_mul_X_pow_eq_monomial]]
      have he : p * (C (h.coeff j.val) * X ^ j.val) = C (h.coeff j.val) * (p * X ^ j.val) := by ring
      rw [he, coeff_C_mul]
      exact mul_comm _ _
    _ = _ := congrArg (fun z => (p * z).coeff (d + i.val)) hre

theorem quotient_mul (p h : R[X]) (d L : ℕ) (hp : p.natDegree ≤ d) (hh : h.natDegree ≤ L) :
    quotient p (p * h) d L = C (p.coeff d ^ (L + 1)) * h := by
  have hc : Matrix.cramer (matrix p d L) (input (p * h) d L) =
      (matrix p d L).det • toFn (L + 1) h := by
    rw [← matrix_action p h d L hh, Matrix.cramer_eq_adjugate_mulVec,
      Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext k
  by_cases hk : k < L + 1
  · rw [quotient, ofFn_coeff_eq_val_of_lt _ hk, hc, matrix_det p d L hp, coeff_C_mul]
    rfl
  · rw [quotient, ofFn_coeff_eq_zero_of_ge _ (by omega), coeff_C_mul]
    have hz : h.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, mul_zero]

theorem selected_map {S : Type*} [CommRing S] (f : R →+* S) (p g : R[X]) (d L : ℕ)
    (s : Fin (L + 1)) :
    (matrix (p.map f) d L).updateCol s (input (g.map f) d L) =
      ((matrix p d L).updateCol s (input g d L)).map f := by
  ext i j
  simp only [selected_entry, Matrix.map_apply, coeff_map, apply_ite f, map_zero]

theorem quotient_map {S : Type*} [CommRing S] (f : R →+* S) (p g : R[X]) (d L : ℕ) :
    (quotient p g d L).map f = quotient (p.map f) (g.map f) d L := by
  ext k
  rw [coeff_map, quotient_coeff, quotient_coeff]
  by_cases hk : k < L + 1
  · rw [dite_eq_left hk, dite_eq_left hk, selected_map, RingHom.map_det]
    rfl
  · rw [dite_eq_right hk, dite_eq_right hk, map_zero]

theorem quotient_coeff_size (p g : ℤ[X]) (d L B k : ℕ)
    (hp : ∀ i, (p.coeff i).natAbs ≤ 2 ^ B) (hg : ∀ i, (g.coeff i).natAbs ≤ 2 ^ B) :
    ((quotient p g d L).coeff k).natAbs.size ≤
      (L + 1).size * (L + 1) + (L + 1) * B + 1 := by
  rw [quotient_coeff]
  split_ifs with hk
  · have hentry (i j : Fin (L + 1)) :
        (((matrix p d L).updateCol ⟨k, hk⟩ (input g d L)) i j).natAbs ≤ 2 ^ B := by
      rw [selected_entry]
      split_ifs
      · exact hg _
      · exact hp _
      · exact Nat.zero_le _
    have h := IntegerModular.det_natAbs_size_le ((matrix p d L).updateCol ⟨k, hk⟩ (input g d L))
      (fun _ => B) hentry
    simpa only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul] using h
  · exact Nat.zero_le _

end LeanCanny.Algebra.ScaledPolynomialQuotient
