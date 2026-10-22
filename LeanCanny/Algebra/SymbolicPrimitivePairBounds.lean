/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicPrimitivePair
public import LeanCanny.Algebra.PolynomialKronecker

/-! # Bounds for the actual symbolic primitive-pair resultant -/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicPrimitivePair
open Polynomial SymbolicScaledSquarefree
open scoped Classical BigOperators
attribute [local irreducible] Matrix.det shiftFamily
set_option maxHeartbeats 150000

theorem shift_inner_degree (p : Polynomial Coefficient) (c E : ℕ)
    (hE : ∀ k, (p.coeff k).natDegree ≤ E) (i j : ℕ) :
    (((shiftFamily p c).coeff i).coeff j).natDegree ≤ E := by
  rw [shiftFamily_coeff_coeff]
  calc
    _ ≤ ((i + j).choose i : Coefficient).natDegree + (p.coeff (i + j)).natDegree +
        i * (-(c : Coefficient)).natDegree :=
      natDegree_mul_le.trans (Nat.add_le_add natDegree_mul_le natDegree_pow_le)
    _ ≤ E := by simpa only [natDegree_natCast, natDegree_neg, Nat.zero_add, Nat.mul_zero,
      Nat.add_zero] using hE (i + j)

theorem resultant_inner_degree (p q : Polynomial Coefficient) (c Ep Eq : ℕ)
    (hp : ∀ k, (p.coeff k).natDegree ≤ Ep) (hq : ∀ k, (q.coeff k).natDegree ≤ Eq) (k : ℕ) :
    ((cannyResultant p q c).coeff k).natDegree ≤ (p.natDegree + q.natDegree) * (Ep + Eq) := by
  have he (r s : Fin (p.natDegree + q.natDegree)) (i : ℕ) :
      (((Polynomial.sylvester (shiftFamily p c) (q.map C) p.natDegree q.natDegree r s).coeff i).natDegree) ≤ Ep + Eq := by
    induction s using Fin.addCases <;>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
    · split_ifs
      · simp only [coeff_map, coeff_C]
        split_ifs
        · exact (hq _).trans (Nat.le_add_left Eq Ep)
        · simp
      · simp
    · split_ifs
      · exact (shift_inner_degree p c Ep hp _ _).trans (Nat.le_add_right Ep Eq)
      · simp
  have h := PolynomialKronecker.determinant_inner_degree
    (Polynomial.sylvester (shiftFamily p c) (q.map C) p.natDegree q.natDegree)
    (fun _ => Ep + Eq) he k
  simpa only [cannyResultant, Polynomial.resultant, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] using h

theorem det_nestedMass_le_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial Coefficient)) (b : ℕ)
    (hb : ∀ r s, NestedMass.mass (A r s) ≤ 2 ^ b) :
    NestedMass.mass A.det ≤ 2 ^ ((Fintype.card ι).size * Fintype.card ι + Fintype.card ι * b) := by
  have hd := NestedMass.det_le A (2 ^ b) hb
  have hf : (Fintype.card ι).factorial ≤ 2 ^ ((Fintype.card ι).size * Fintype.card ι) :=
    (Nat.factorial_le_pow _).trans (by
      simpa only [← pow_mul] using Nat.pow_le_pow_left (Nat.lt_size_self (Fintype.card ι)).le (Fintype.card ι))
  calc
    _ ≤ _ := hd
    _ ≤ 2 ^ ((Fintype.card ι).size * Fintype.card ι) * (2 ^ b) ^ Fintype.card ι := Nat.mul_le_mul_right _ hf
    _ = _ := by rw [← pow_mul, ← pow_add, Nat.mul_comm b]

def shiftExponent (D c b : ℕ) : ℕ := (D + 1).size + D + b + (c + 1).size * D

theorem shift_coefficient_mass (p : Polynomial Coefficient) (c b : ℕ)
    (hb : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ b) (i j : ℕ) :
    coefficientMass (((shiftFamily p c).coeff i).coeff j) ≤
      2 ^ (p.natDegree + b + (c + 1).size * p.natDegree) := by
  rw [shiftFamily_coeff_coeff]
  by_cases hij : i + j ≤ p.natDegree
  · have he : coefficientMass (((i + j).choose i : Coefficient)) = (i + j).choose i := by
      simpa only [map_natCast, Int.natAbs_natCast] using coefficientMass_C (((i + j).choose i : ℕ) : ℤ)
    have hc : coefficientMass (-(c : Coefficient)) = c := by
      simpa only [map_natCast, Int.natAbs_natCast, coefficientMass_neg] using coefficientMass_C (c : ℤ)
    have hchoose := (Nat.choose_le_two_pow (i + j) i).trans (Nat.pow_le_pow_right (by decide) hij)
    have hpower : c ^ i ≤ (2 ^ (c + 1).size) ^ p.natDegree :=
      (Nat.pow_le_pow_left ((Nat.le_succ c).trans (Nat.lt_size_self (c + 1)).le) i).trans
        (Nat.pow_le_pow_right (by positivity) (by omega))
    calc
      _ ≤ coefficientMass (((i + j).choose i : Coefficient)) * coefficientMass (p.coeff (i + j)) *
          coefficientMass (-(c : Coefficient)) ^ i :=
        (coefficientMass_mul_le _ _).trans (Nat.mul_le_mul (coefficientMass_mul_le _ _) (coefficientMass_pow_le _ _))
      _ ≤ 2 ^ p.natDegree * 2 ^ b * (2 ^ (c + 1).size) ^ p.natDegree := by
        rw [he, hc]
        exact Nat.mul_le_mul (Nat.mul_le_mul hchoose (hb _)) hpower
      _ = _ := by rw [← pow_mul, ← pow_add, ← pow_add]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i + j), mul_zero, zero_mul, coefficientMass_zero]
    exact Nat.zero_le _

theorem shift_mass (p : Polynomial Coefficient) (c b : ℕ)
    (hb : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ b) (i : ℕ) :
    NestedMass.mass ((shiftFamily p c).coeff i) ≤ 2 ^ shiftExponent p.natDegree c b := by
  have h := NestedMass.le_pow ((shiftFamily p c).coeff i) p.natDegree
    (p.natDegree + b + (c + 1).size * p.natDegree)
    ((shiftFamily_coeff_natDegree_le _ _ _).trans (Nat.sub_le _ _))
    (shift_coefficient_mass p c b hb i)
  simpa only [shiftExponent, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def resultantMassExponent (m n c bp bq : ℕ) : ℕ :=
  (m + n).size * (m + n) + (m + n) * (shiftExponent m c bp + bq)

theorem resultant_mass (p q : Polynomial Coefficient) (c bp bq : ℕ)
    (hp : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ bp)
    (hq : ∀ k, coefficientMass (q.coeff k) ≤ 2 ^ bq) :
    NestedMass.mass (cannyResultant p q c) ≤
      2 ^ resultantMassExponent p.natDegree q.natDegree c bp bq := by
  have he (r s : Fin (p.natDegree + q.natDegree)) :
      NestedMass.mass (Polynomial.sylvester (shiftFamily p c) (q.map C) p.natDegree q.natDegree r s) ≤
        2 ^ (shiftExponent p.natDegree c bp + bq) := by
    induction s using Fin.addCases <;>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
    · split_ifs
      · simpa only [coeff_map, NestedMass.C] using (hq _).trans
          (Nat.pow_le_pow_right (by decide) (Nat.le_add_left bq (shiftExponent p.natDegree c bp)))
      · simp
    · split_ifs
      · exact (shift_mass p c bp hp _).trans
          (Nat.pow_le_pow_right (by decide) (Nat.le_add_right (shiftExponent p.natDegree c bp) bq))
      · simp
  have h := det_nestedMass_le_pow _ (shiftExponent p.natDegree c bp + bq) he
  simpa only [cannyResultant, Polynomial.resultant, Fintype.card_fin, resultantMassExponent] using h

theorem discriminant_mass (p : Polynomial Coefficient) (b : ℕ)
    (hb : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ b) :
    coefficientMass (discriminant p) ≤ 2 ^ gcdMassExponent p.natDegree b := by
  have hp (i : ℕ) : coefficientMass (p.coeff i) ≤ 2 ^ (b + p.natDegree.size) :=
    (hb i).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  have he (r s : Fin (p.natDegree + p.derivative.natDegree)) :
      coefficientMass (Polynomial.sylvester p p.derivative p.natDegree p.derivative.natDegree r s) ≤
        2 ^ (b + p.natDegree.size) := by
    induction s using Fin.addCases <;>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
    all_goals split_ifs
    all_goals first | exact hp _ | exact derivative_coefficient_mass p b hb _ | simp
  have h := det_coefficientMass_le_pow _ (b + p.natDegree.size) he
  simp only [Fintype.card_fin] at h
  apply h.trans
  apply Nat.pow_le_pow_right (by decide)
  have hn := natDegree_derivative_le p
  have hN : p.natDegree + p.derivative.natDegree ≤ 2 * p.natDegree := by omega
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.size_le_size hN) hN) (Nat.mul_le_mul_right _ hN)

end LeanCanny.Algebra.SymbolicPrimitivePair
