/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PseudoRemainderBudget

/-! # Tarski-seed bit budgets from the original two polynomials -/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial

open LeanCanny.Encoding
open scoped BigOperators

/-- Differentiating multiplies coefficient mass by at most the degree. -/
theorem coefficientMass_derivative_le (p : ℤ[X]) :
    coefficientMass p.derivative ≤ p.natDegree * coefficientMass p := by
  have hsum := p.as_sum_range
  have hder : p.derivative =
      ∑ i ∈ Finset.range (p.natDegree + 1), (monomial i (p.coeff i)).derivative := by
    conv_lhs => rw [hsum]
    rw [derivative_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1),
        coefficientMass ((monomial i (p.coeff i)).derivative) := by
      rw [hder]
      exact coefficientMass_sum_le _ _
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i).natAbs * i := by
      simp only [derivative_monomial, coefficientMass_monomial, Int.natAbs_mul, Int.natAbs_natCast]
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i).natAbs * p.natDegree :=
      Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ (by have := Finset.mem_range.mp hi; omega)
    _ = _ := by
      rw [← Finset.sum_mul, coefficientMass,
        p.sum_over_range' (fun _ => rfl) (p.natDegree + 1) (by omega), mul_comm]

namespace TarskiSeedBits

def productMassCode (degree headMass queryMass : List Bool) : List Bool :=
  BinaryNat.add (pair (BinaryNat.add (pair headMass queryMass)) (BinaryNatCode.encode degree.length))

theorem productMassCode_mem_FP {degree bp bf : List Bool → List Bool}
    (hd : degree ∈ FP) (hp : bp ∈ FP) (hf : bf ∈ FP) :
    (fun c => productMassCode (degree c) (bp c) (bf c)) ∈ FP := by
  have hl := bits_mem_FP (UnaryFn.length hd)
  have hs := mem_FP_comp (mem_FP_pair hp hf) BinaryNat.add_mem_FP
  have h := mem_FP_comp (mem_FP_pair hs hl) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := fun c => productMassCode (degree c) (bp c) (bf c)) h ?_
  intro c
  simp only [productMassCode, Function.comp_apply, BinaryNatCode.encode]

theorem productMassCode_eq (degree bp bf : List Bool) : productMassCode degree bp bf =
    BinaryNatCode.encode (Nat.fromBitsLE bp + Nat.fromBitsLE bf + degree.length) := by
  simp only [productMassCode, BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem product_mass_le (p f : ℤ[X]) (degree bp bf : List Bool)
    (hd : p.natDegree ≤ Nat.fromBitsLE degree)
    (hp : coefficientMass p ≤ 2 ^ Nat.fromBitsLE bp)
    (hf : coefficientMass f ≤ 2 ^ Nat.fromBitsLE bf) :
    coefficientMass (f * p.derivative) ≤ 2 ^ Nat.fromBitsLE (productMassCode degree bp bf) := by
  have hdegree : p.natDegree ≤ 2 ^ degree.length :=
    hd.trans (Nat.fromBitsLE_lt_pow_length degree).le
  calc
    _ ≤ coefficientMass f * coefficientMass p.derivative := coefficientMass_mul_le _ _
    _ ≤ coefficientMass f * (p.natDegree * coefficientMass p) :=
      Nat.mul_le_mul_left _ (coefficientMass_derivative_le p)
    _ ≤ 2 ^ Nat.fromBitsLE bf * (2 ^ degree.length * 2 ^ Nat.fromBitsLE bp) :=
      Nat.mul_le_mul hf (Nat.mul_le_mul hdegree hp)
    _ = _ := by
      rw [productMassCode_eq]
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, ← pow_add]
      congr 1
      omega

def seedBudgetCode (degree queryBound headMass queryMass : List Bool) : List Bool :=
  PseudoRemainder.budgetCode (BinaryNat.add (pair degree queryBound)) headMass
    (productMassCode degree headMass queryMass)

theorem seedBudgetCode_mem_FP {degree queryBound bp bf : List Bool → List Bool}
    (hd : degree ∈ FP) (hq : queryBound ∈ FP) (hp : bp ∈ FP) (hf : bf ∈ FP) :
    (fun c => seedBudgetCode (degree c) (queryBound c) (bp c) (bf c)) ∈ FP := by
  have hD := mem_FP_comp (mem_FP_pair hd hq) BinaryNat.add_mem_FP
  have h := PseudoRemainder.budgetCode_mem_FP hD hp (productMassCode_mem_FP hd hp hf)
  refine mem_FP_of_eq (g := fun c => seedBudgetCode (degree c) (queryBound c) (bp c) (bf c)) h ?_
  intro c
  simp only [seedBudgetCode, Function.comp_apply]

theorem seed_coeff_size_le (p f : ℤ[X]) (degree queryBound bp bf : List Bool)
    (hd : p.natDegree ≤ Nat.fromBitsLE degree)
    (hp : coefficientMass p ≤ 2 ^ Nat.fromBitsLE bp)
    (hf : coefficientMass f ≤ 2 ^ Nat.fromBitsLE bf) (i : ℕ) :
    ((PseudoRemainder.seed p f (Nat.fromBitsLE degree)
      (Nat.fromBitsLE degree + Nat.fromBitsLE queryBound)).coeff i).natAbs.size ≤
      Nat.fromBitsLE (seedBudgetCode degree queryBound bp bf) := by
  simp only [seedBudgetCode, PseudoRemainder.budgetCode_eq, BinaryNat.add_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, PseudoRemainder.seed]
  exact PseudoRemainder.iterate_coeff_size_le p (f * p.derivative) _ _ _ _ i hp
    (product_mass_le p f degree bp bf hd hp hf)

end TarskiSeedBits
end LeanCanny.Algebra
