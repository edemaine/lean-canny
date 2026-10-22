/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicPrimitivePairBounds

/-! # Symbolic coefficient mass of the explicit pair recovery formulas -/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicPrimitivePair
open Polynomial SymbolicScaledSquarefree
open scoped Classical BigOperators
attribute [local irreducible] Matrix.det shiftFamily
set_option maxHeartbeats 150000

theorem recovery_mass (p q : Polynomial Coefficient) (c bp bq r : ℕ)
    (hp : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ bp)
    (hq : ∀ k, coefficientMass (q.coeff k) ≤ 2 ^ bq) :
    NestedMass.mass ((recoverySubresultant p q c).coeff r) ≤
      2 ^ resultantMassExponent p.natDegree q.natDegree c bp bq := by
  rw [recoverySubresultant, Subresultant.coeff]
  split_ifs
  · let N := (p.natDegree - 1) + (q.natDegree - 1)
    let B := shiftExponent p.natDegree c bp + bq
    have he (i j : Fin N) : NestedMass.mass
        (Subresultant.minor (shiftFamily p c) (q.map C) p.natDegree q.natDegree 1 r i j) ≤ 2 ^ B := by
      induction j using Fin.addCases <;>
        simp only [Subresultant.minor, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right, Subresultant.band]
      · split_ifs
        · simpa only [coeff_map, NestedMass.C] using (hq _).trans
            (Nat.pow_le_pow_right (by decide) (Nat.le_add_left bq (shiftExponent p.natDegree c bp)))
        · simp
      · split_ifs
        · exact (shift_mass p c bp hp _).trans
            (Nat.pow_le_pow_right (by decide) (Nat.le_add_right (shiftExponent p.natDegree c bp) bq))
        · simp
    have h := det_nestedMass_le_pow _ B he
    simp only [Fintype.card_fin] at h
    apply h.trans
    apply Nat.pow_le_pow_right (by decide)
    have hN : N ≤ p.natDegree + q.natDegree := by dsimp [N]; omega
    exact Nat.add_le_add (Nat.mul_le_mul (Nat.size_le_size hN) hN) (Nat.mul_le_mul_right B hN)
  · simp

def coordinateMassExponent (m n c bp bq : ℕ) : ℕ :=
  resultantMassExponent m n c bp bq + shiftExponent m c bp + bq

theorem coordinateCoefficient_mass (p q : Polynomial Coefficient) (c bp bq r : ℕ)
    (hp : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ bp)
    (hq : ∀ k, coefficientMass (q.coeff k) ≤ 2 ^ bq) :
    NestedMass.mass (coordinateCoefficient p q c r) ≤
      2 ^ coordinateMassExponent p.natDegree q.natDegree c bp bq := by
  unfold coordinateCoefficient
  split_ifs
  · exact (show NestedMass.mass (C (q.coeff r)) ≤ 2 ^ bq by
      simpa only [NestedMass.C] using hq r).trans
      (Nat.pow_le_pow_right (by decide) (by unfold coordinateMassExponent; omega))
  · exact (shift_mass p c bp hp r).trans
      (Nat.pow_le_pow_right (by decide) (by unfold coordinateMassExponent; omega))
  · exact (recovery_mass p q c bp bq r hp hq).trans
      (Nat.pow_le_pow_right (by decide) (by unfold coordinateMassExponent; omega))

theorem denominator_mass (p q : Polynomial Coefficient) (c bp bq : ℕ)
    (hp : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ bp)
    (hq : ∀ k, coefficientMass (q.coeff k) ≤ 2 ^ bq) :
    NestedMass.mass (PrimitivePair.denominator p q c) ≤
      2 ^ coordinateMassExponent p.natDegree q.natDegree c bp bq :=
  coordinateCoefficient_mass p q c bp bq 1 hp hq

theorem rightNumerator_mass (p q : Polynomial Coefficient) (c bp bq : ℕ)
    (hp : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ bp)
    (hq : ∀ k, coefficientMass (q.coeff k) ≤ 2 ^ bq) :
    NestedMass.mass (PrimitivePair.rightNumerator p q c) ≤
      2 ^ coordinateMassExponent p.natDegree q.natDegree c bp bq := by
  rw [PrimitivePair.rightNumerator, NestedMass.neg]
  exact coordinateCoefficient_mass p q c bp bq 0 hp hq

theorem leftNumerator_mass (p q : Polynomial Coefficient) (c bp bq : ℕ)
    (hp : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ bp)
    (hq : ∀ k, coefficientMass (q.coeff k) ≤ 2 ^ bq) :
    NestedMass.mass (PrimitivePair.leftNumerator p q c) ≤
      2 ^ (coordinateMassExponent p.natDegree q.natDegree c bp bq + (c + 1).size) := by
  have hmone : coefficientMass (1 : Coefficient) = 1 := by
    simpa only [Polynomial.C_1, Int.natAbs_one] using coefficientMass_C (1 : ℤ)
  have hmX : NestedMass.mass (X : Polynomial Coefficient) = 1 := by
    simpa only [monomial_one_one_eq_X, hmone] using NestedMass.monomial 1 (1 : Coefficient)
  have hmc : NestedMass.mass (C (c : Coefficient)) = c := by
    rw [NestedMass.C]
    simpa only [map_natCast, Int.natAbs_natCast] using coefficientMass_C (c : ℤ)
  let B := coordinateMassExponent p.natDegree q.natDegree c bp bq
  rw [PrimitivePair.leftNumerator]
  calc
    _ ≤ NestedMass.mass (X * PrimitivePair.denominator p q c) +
        NestedMass.mass (C (c : Coefficient) * coordinateNumerator p q c) := NestedMass.add_le _ _
    _ ≤ NestedMass.mass X * NestedMass.mass (PrimitivePair.denominator p q c) +
        NestedMass.mass (C (c : Coefficient)) * NestedMass.mass (coordinateNumerator p q c) :=
      Nat.add_le_add (NestedMass.mul_le _ _) (NestedMass.mul_le _ _)
    _ ≤ 1 * 2 ^ B + c * 2 ^ B := by
      rw [hmX, hmc]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ (denominator_mass p q c bp bq hp hq))
        (Nat.mul_le_mul_left _ (coordinateCoefficient_mass p q c bp bq 0 hp hq))
    _ = (c + 1) * 2 ^ B := by ring
    _ ≤ 2 ^ (c + 1).size * 2 ^ B := Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
    _ = _ := by rw [← pow_add, Nat.add_comm]

theorem recovery_inner_degree (p q : Polynomial Coefficient) (c Ep Eq : ℕ)
    (hp : ∀ k, (p.coeff k).natDegree ≤ Ep) (hq : ∀ k, (q.coeff k).natDegree ≤ Eq) (r k : ℕ) :
    (((recoverySubresultant p q c).coeff r).coeff k).natDegree ≤
      (p.natDegree + q.natDegree) * (Ep + Eq) := by
  rw [recoverySubresultant, Subresultant.coeff]
  split_ifs
  · let N := (p.natDegree - 1) + (q.natDegree - 1)
    have he (i j : Fin N) (d : ℕ) :
        ((Subresultant.minor (shiftFamily p c) (q.map C) p.natDegree q.natDegree 1 r i j).coeff d).natDegree ≤ Ep + Eq := by
      induction j using Fin.addCases <;>
        simp only [Subresultant.minor, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right, Subresultant.band]
      · split_ifs
        · simp only [coeff_map, coeff_C]
          split_ifs
          · exact (hq _).trans (Nat.le_add_left Eq Ep)
          · simp
        · simp
      · split_ifs
        · exact (shift_inner_degree p c Ep hp _ _).trans (Nat.le_add_right Ep Eq)
        · simp
    have h := PolynomialKronecker.determinant_inner_degree _ (fun _ : Fin N => Ep + Eq) he k
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    exact h.trans (Nat.mul_le_mul_right (Ep + Eq) (by dsimp [N]; omega))
  · simp

theorem coordinateCoefficient_inner_degree (p q : Polynomial Coefficient) (c Ep Eq : ℕ)
    (hp : ∀ k, (p.coeff k).natDegree ≤ Ep) (hq : ∀ k, (q.coeff k).natDegree ≤ Eq) (r k : ℕ) :
    ((coordinateCoefficient p q c r).coeff k).natDegree ≤
      (p.natDegree + q.natDegree + 1) * (Ep + Eq) := by
  have hb : Ep + Eq ≤ (p.natDegree + q.natDegree + 1) * (Ep + Eq) := by nlinarith
  unfold coordinateCoefficient
  split_ifs
  · rw [coeff_C]
    split_ifs
    · exact (hq _).trans ((Nat.le_add_left Eq Ep).trans hb)
    · simp
  · exact (shift_inner_degree p c Ep hp _ _).trans ((Nat.le_add_right Ep Eq).trans hb)
  · exact (recovery_inner_degree p q c Ep Eq hp hq r k).trans (Nat.mul_le_mul_right _ (Nat.le_succ _))

theorem numerator_inner_degree (p q : Polynomial Coefficient) (c Ep Eq : ℕ)
    (hp : ∀ k, (p.coeff k).natDegree ≤ Ep) (hq : ∀ k, (q.coeff k).natDegree ≤ Eq) (k : ℕ) :
    ((coordinateNumerator p q c).coeff k).natDegree ≤
      (p.natDegree + q.natDegree + 1) * (Ep + Eq) :=
  coordinateCoefficient_inner_degree p q c Ep Eq hp hq 0 k

theorem denominator_inner_degree (p q : Polynomial Coefficient) (c Ep Eq : ℕ)
    (hp : ∀ k, (p.coeff k).natDegree ≤ Ep) (hq : ∀ k, (q.coeff k).natDegree ≤ Eq) (k : ℕ) :
    ((PrimitivePair.denominator p q c).coeff k).natDegree ≤
      (p.natDegree + q.natDegree + 1) * (Ep + Eq) :=
  coordinateCoefficient_inner_degree p q c Ep Eq hp hq 1 k

theorem rightNumerator_inner_degree (p q : Polynomial Coefficient) (c Ep Eq : ℕ)
    (hp : ∀ k, (p.coeff k).natDegree ≤ Ep) (hq : ∀ k, (q.coeff k).natDegree ≤ Eq) (k : ℕ) :
    ((PrimitivePair.rightNumerator p q c).coeff k).natDegree ≤
      (p.natDegree + q.natDegree + 1) * (Ep + Eq) := by
  rw [PrimitivePair.rightNumerator, coeff_neg, natDegree_neg]
  exact coordinateCoefficient_inner_degree p q c Ep Eq hp hq 0 k

theorem leftNumerator_inner_degree (p q : Polynomial Coefficient) (c Ep Eq : ℕ)
    (hp : ∀ k, (p.coeff k).natDegree ≤ Ep) (hq : ∀ k, (q.coeff k).natDegree ≤ Eq) (k : ℕ) :
    ((PrimitivePair.leftNumerator p q c).coeff k).natDegree ≤
      (p.natDegree + q.natDegree + 1) * (Ep + Eq) := by
  rw [PrimitivePair.leftNumerator_coeff]
  apply (natDegree_add_le _ _).trans
  apply max_le
  · split_ifs
    · exact denominator_inner_degree p q c Ep Eq hp hq _
    · simp
  · apply natDegree_mul_le.trans
    simpa only [natDegree_natCast, Nat.zero_add] using
      numerator_inner_degree p q c Ep Eq hp hq k

end LeanCanny.Algebra.SymbolicPrimitivePair
