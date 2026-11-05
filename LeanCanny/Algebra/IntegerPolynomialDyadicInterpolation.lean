/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerPolynomialDyadicGrowth
public import LeanCanny.Algebra.CoefficientMass
public import LeanCanny.Computation.PolyTimeBinaryNat
public import Mathlib.LinearAlgebra.Lagrange

/-! # Coefficient mass from actual values at integer dyadic nodes

Lagrange denominators are nonzero integers, so their absolute values are at
least one. The final numerical exponent requires no interpolation algorithm.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialDyadic
open Polynomial
open scoped Classical BigOperators

noncomputable def node {K : ℕ} (C : ℕ) (i : Fin (K + 1)) : ℤ := 2 ^ (C + i.val)

noncomputable def numerator (C K : ℕ) (i : Fin (K + 1)) : Polynomial ℤ :=
  ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (node C j))

noncomputable def denominator (C K : ℕ) (i : Fin (K + 1)) : ℤ :=
  ∏ j ∈ Finset.univ.erase i, (node C i - node C j)

theorem node_injective (C K : ℕ) : Function.Injective (node (K := K) C) := by
  intro i j hij
  have H : C + i.val = C + j.val := Int.pow_right_injective (by decide : 1 < (2 : ℤ).natAbs) hij
  exact Fin.ext (by omega)

theorem denominator_ne_zero (C K : ℕ) (i : Fin (K + 1)) : denominator C K i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro he
  exact (Finset.mem_erase.mp hj).1 ((node_injective C K he).symm)

theorem basis_eq (C K : ℕ) (i : Fin (K + 1)) :
    Lagrange.basis Finset.univ (fun j : Fin (K + 1) => (node C j : ℝ)) i =
      Polynomial.C ((denominator C K i : ℝ)⁻¹) * (numerator C K i).map (Int.castRingHom ℝ) := by
  simp only [Lagrange.basis, Lagrange.basisDivisor, numerator, denominator,
    Finset.prod_mul_distrib, ← map_prod, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Int.cast_prod, Int.cast_sub, Finset.prod_inv_distrib, Int.coe_castRingHom]

private theorem mass_X : coefficientMass (Polynomial.X : Polynomial ℤ) = 1 := by
  simpa only [Polynomial.monomial_one_one_eq_X, Int.natAbs_one] using coefficientMass_monomial 1 (1 : ℤ)

theorem node_natAbs {K : ℕ} (C : ℕ) (i : Fin (K + 1)) : (node C i).natAbs = 2 ^ (C + i.val) := by
  simp only [node, Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl]

theorem numerator_mass (C K : ℕ) (i : Fin (K + 1)) :
    coefficientMass (numerator C K i) ≤ 2 ^ (K * (C + K + 1)) := by
  have HF (j : Fin (K + 1)) :
      coefficientMass (Polynomial.X - Polynomial.C (node C j)) ≤ 2 ^ (C + K + 1) := by
    have H := (coefficientMass_sub_le (Polynomial.X : Polynomial ℤ) (Polynomial.C (node C j)))
    rw [mass_X, coefficientMass_C, node_natAbs] at H
    have HM : 2 ^ (C + j.val) ≤ 2 ^ (C + K) := Nat.pow_le_pow_right (by decide) (by omega)
    have HP := Nat.one_le_two_pow (n := C + K)
    calc
      _ ≤ 1 + 2 ^ (C + j.val) := H
      _ ≤ 2 ^ (C + K) + 2 ^ (C + K) := Nat.add_le_add HP HM
      _ = 2 ^ (C + K + 1) := by rw [pow_succ]; omega
  apply (coefficientMass_prod_le (Finset.univ.erase i) _).trans
  calc
    _ ≤ ∏ _j ∈ Finset.univ.erase i, 2 ^ (C + K + 1) := Finset.prod_le_prod (fun j _ => HF j)
    _ = 2 ^ (K * (C + K + 1)) := by simp [← pow_mul, Nat.mul_comm]

private theorem eval_node (f : Polynomial ℤ) (C K : ℕ) (i : Fin (K + 1)) :
    (f.map (Int.castRingHom ℝ)).eval (node C i : ℝ) = ((f.eval (node C i) : ℤ) : ℝ) := by
  rw [Polynomial.eval_map]
  simpa only [Int.coe_castRingHom] using
    Polynomial.eval₂_at_apply (p := f) (Int.castRingHom ℝ) (node C i)

private theorem abs_cast_le {z : ℤ} {M : ℕ} (h : z.natAbs ≤ M) : |(z : ℝ)| ≤ (M : ℝ) := by
  have H : (z.natAbs : ℝ) ≤ (M : ℝ) := by exact_mod_cast h
  simpa only [Nat.cast_natAbs, Int.cast_abs] using H

private theorem natAbs_le_of_abs_cast_le {z : ℤ} {M : ℕ} (h : |(z : ℝ)| ≤ (M : ℝ)) : z.natAbs ≤ M := by
  have H : (z.natAbs : ℝ) ≤ (M : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  exact_mod_cast H

theorem coeff_le_of_samples (f : Polynomial ℤ) (C K E : ℕ) (hd : f.natDegree ≤ K)
    (hs : ∀ i : Fin (K + 1), (f.eval (node C i)).natAbs ≤ 2 ^ E) (k : ℕ) :
    (f.coeff k).natAbs ≤ (K + 1) * (2 ^ E * 2 ^ (K * (C + K + 1))) := by
  have hi : Set.InjOn (fun i : Fin (K + 1) => (node C i : ℝ))
      ((Finset.univ : Finset (Fin (K + 1))) : Set (Fin (K + 1))) := by
    intro i _ j _ hij
    exact node_injective C K (Int.cast_injective hij)
  have hd' : (f.map (Int.castRingHom ℝ)).degree <
      ((Finset.univ : Finset (Fin (K + 1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact Polynomial.degree_le_natDegree.trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le (Polynomial.natDegree_map_le.trans hd)))
  have HE := Lagrange.eq_interpolate (f := f.map (Int.castRingHom ℝ)) hi hd'
  have HC := congrArg (fun q : Polynomial ℝ => q.coeff k) HE
  simp only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_map, basis_eq, eval_node, Int.coe_castRingHom] at HC
  have HR : |((f.coeff k : ℤ) : ℝ)| ≤
      ((K + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ E * (2 : ℝ) ^ (K * (C + K + 1))) := by
    rw [HC]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i : Fin (K + 1), (2 : ℝ) ^ E * (2 : ℝ) ^ (K * (C + K + 1)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_mul]
        have HV : |((f.eval (node C i) : ℤ) : ℝ)| ≤ (2 : ℝ) ^ E := by
          simpa only [Nat.cast_pow, Nat.cast_ofNat] using abs_cast_le (hs i)
        have HN : |(((numerator C K i).coeff k : ℤ) : ℝ)| ≤ (2 : ℝ) ^ (K * (C + K + 1)) := by
          simpa only [Nat.cast_pow, Nat.cast_ofNat] using
            abs_cast_le ((coeff_natAbs_le_coefficientMass (numerator C K i) k).trans (numerator_mass C K i))
        have HD : (1 : ℝ) ≤ |(denominator C K i : ℝ)| := by
          have H : (1 : ℝ) ≤ ((denominator C K i).natAbs : ℝ) := by
            exact_mod_cast (Nat.succ_le_of_lt (Int.natAbs_pos.mpr (denominator_ne_zero C K i)))
          simpa only [Nat.cast_natAbs, Int.cast_abs] using H
        have HI : |(denominator C K i : ℝ)⁻¹| ≤ 1 := by
          rw [abs_inv]
          simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) HD
        have HP := mul_le_mul HI HN (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        exact (mul_le_mul HV HP (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)).trans_eq
          (by rw [one_mul])
      _ = _ := by simp
  apply natAbs_le_of_abs_cast_le
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using HR

def massBudget (C K H : ℕ) : ℕ := H + 2 * K * (C + K) + K + 2 * (K + 1).size

theorem massBudget_binary {C K H : List Bool → ℕ} (hC : BinaryFn C) (hK : BinaryFn K) (hH : BinaryFn H) :
    BinaryFn (fun q => massBudget (C q) (K q) (H q)) :=
  ((hH.add (((BinaryFn.const 2).mul hK).mul (hC.add hK))).add hK).add
    ((BinaryFn.const 2).mul (hK.add (BinaryFn.const 1)).size)

theorem coefficientMass_le (f : Polynomial ℤ) (C K H : ℕ)
    (h : ∀ r, C ≤ r → (f.eval ((2 : ℤ) ^ r)).natAbs ≤ 2 ^ (K * r + H)) :
    coefficientMass f ≤ 2 ^ massBudget C K H := by
  have hd := natDegree_le f C K H h
  let E := K * (C + K) + H
  let N := K * (C + K + 1)
  have hs (i : Fin (K + 1)) : (f.eval (node C i)).natAbs ≤ 2 ^ E := by
    apply (h (C + i.val) (by omega)).trans
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.add_le_add_right (Nat.mul_le_mul_left K (Nat.add_le_add_left (by omega : i.val ≤ K) C)) H
  have HC (k : ℕ) : (f.coeff k).natAbs ≤ 2 ^ ((K + 1).size + E + N) := by
    apply (coeff_le_of_samples f C K E hd hs k).trans
    calc
      _ ≤ 2 ^ (K + 1).size * (2 ^ E * 2 ^ N) :=
        Nat.mul_le_mul_right _ (Nat.lt_size_self (K + 1)).le
      _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega
  apply (coefficientMass_le_pow_of_degree_coeff f K _ hd HC).trans_eq
  congr 1
  dsimp only [E, N, massBudget]
  ring

theorem degree_mass_of_growth (f : Polynomial ℤ) (C K H : ℕ)
    (h : ∀ r, C ≤ r → (f.eval ((2 : ℤ) ^ r)).natAbs ≤ 2 ^ (K * r + H)) :
    f.natDegree ≤ K ∧ coefficientMass f ≤ 2 ^ massBudget C K H :=
  ⟨natDegree_le f C K H h, coefficientMass_le f C K H h⟩

end LeanCanny.Algebra.IntegerPolynomialDyadic
