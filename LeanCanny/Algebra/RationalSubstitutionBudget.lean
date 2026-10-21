/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitutionBounds
public import LeanCanny.Encoding.BinaryMulFP
public import LeanCanny.Tactic.PolyTime

/-!
# FP binary budget writers for rational substitution

Arbitrary binary metadata words specify an arity allowance `A`, variable-degree
allowance `D`, coordinate-degree allowance `E`, coordinate coefficient-mass bits
`b`, and source coefficient-mass bits `s`. The writers return `2*A*D*E` and
`s+2*A*D*b+1` without expanding a polynomial or a numeric magnitude to unary.
Semantic metadata bounds imply the resulting degree and coefficient budgets.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution
open Polynomial

open LeanCanny.Encoding

def degreeCode (a d e : List Bool) : List Bool :=
  BinaryNat.mul (pair (BinaryNat.mul (pair (BinaryNat.add (pair a a)) d)) e)

def budgetCode (a d b s : List Bool) : List Bool :=
  BinaryNat.succ (BinaryNat.add (pair s (degreeCode a d b)))

def sourceBudgetCode (a d b : List Bool) : List Bool :=
  BinaryNat.add (pair b (BinaryNat.mul (pair a (BinaryNatCode.encode (BinaryNat.succ d).length))))

def fullBudgetCode (a d b b₀ : List Bool) : List Bool := budgetCode a d b (sourceBudgetCode a d b₀)

def coefficientBudgetCode (a d e b b₀ : List Bool) : List Bool :=
  fullBudgetCode a d (sourceBudgetCode [true] e b) b₀

theorem degreeCode_mem_FP {a d e : List Bool → List Bool} (ha : a ∈ FP) (hd : d ∈ FP) (he : e ∈ FP) :
    (fun c => degreeCode (a c) (d c) (e c)) ∈ FP := by
  have hdouble := mem_FP_comp (mem_FP_pair ha ha) BinaryNat.add_mem_FP
  have hprod := mem_FP_comp (mem_FP_pair hdouble hd) BinaryNat.mul_mem_FP
  have h := mem_FP_comp (mem_FP_pair hprod he) BinaryNat.mul_mem_FP
  refine mem_FP_of_eq h ?_
  intro c
  simp only [Function.comp_apply, degreeCode]

theorem budgetCode_mem_FP {a d b s : List Bool → List Bool}
    (ha : a ∈ FP) (hd : d ∈ FP) (hb : b ∈ FP) (hs : s ∈ FP) :
    (fun c => budgetCode (a c) (d c) (b c) (s c)) ∈ FP := by
  have hp := degreeCode_mem_FP ha hd hb
  have hadd := mem_FP_comp (mem_FP_pair hs hp) BinaryNat.add_mem_FP
  have h := mem_FP_comp hadd BinaryNat.succ_mem_FP
  refine mem_FP_of_eq h ?_
  intro c
  simp only [Function.comp_apply, budgetCode]

theorem sourceBudgetCode_mem_FP {a d b : List Bool → List Bool} (ha : a ∈ FP) (hd : d ∈ FP) (hb : b ∈ FP) :
    (fun c => sourceBudgetCode (a c) (d c) (b c)) ∈ FP := by
  have hsize := bits_mem_FP (UnaryFn.length (mem_FP_comp hd BinaryNat.succ_mem_FP))
  have hp := mem_FP_comp (mem_FP_pair ha hsize) BinaryNat.mul_mem_FP
  have h := mem_FP_comp (mem_FP_pair hb hp) BinaryNat.add_mem_FP
  refine mem_FP_of_eq h ?_
  intro c
  simp only [Function.comp_apply, sourceBudgetCode, BinaryNatCode.encode]

theorem fullBudgetCode_mem_FP {a d b b₀ : List Bool → List Bool}
    (ha : a ∈ FP) (hd : d ∈ FP) (hb : b ∈ FP) (h₀ : b₀ ∈ FP) :
    (fun c => fullBudgetCode (a c) (d c) (b c) (b₀ c)) ∈ FP :=
  budgetCode_mem_FP ha hd hb (sourceBudgetCode_mem_FP ha hd h₀)

theorem coefficientBudgetCode_mem_FP {a d e b b₀ : List Bool → List Bool}
    (ha : a ∈ FP) (hd : d ∈ FP) (he : e ∈ FP) (hb : b ∈ FP) (h₀ : b₀ ∈ FP) :
    (fun c => coefficientBudgetCode (a c) (d c) (e c) (b c) (b₀ c)) ∈ FP :=
  fullBudgetCode_mem_FP ha hd (sourceBudgetCode_mem_FP (constFn_mem_FP [true]) he hb) h₀

theorem degreeCode_code (a d e : List Bool) : degreeCode a d e =
    BinaryNatCode.encode (2 * Nat.fromBitsLE a * Nat.fromBitsLE d * Nat.fromBitsLE e) := by
  simp only [degreeCode, BinaryNat.mul_pair, BinaryNat.add_pair, Nat.fromBitsLE_bits,
    BinaryNatCode.encode, two_mul]

theorem budgetCode_code (a d b s : List Bool) : budgetCode a d b s =
    BinaryNatCode.encode (Nat.fromBitsLE s + 2 * Nat.fromBitsLE a * Nat.fromBitsLE d * Nat.fromBitsLE b + 1) := by
  simp only [budgetCode, degreeCode_code, BinaryNat.add_pair, BinaryNat.succ_eq_bits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem sourceBudgetCode_code (a d b : List Bool) : sourceBudgetCode a d b =
    BinaryNatCode.encode (Nat.fromBitsLE b + Nat.fromBitsLE a * (Nat.fromBitsLE d + 1).size) := by
  simp only [sourceBudgetCode, BinaryNat.add_pair, BinaryNat.mul_pair, BinaryNat.succ_eq_bits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.size_eq_bits_len]

theorem fullBudgetCode_code (a d b b₀ : List Bool) : fullBudgetCode a d b b₀ =
    BinaryNatCode.encode (Nat.fromBitsLE b₀ + Nat.fromBitsLE a * (Nat.fromBitsLE d + 1).size +
      2 * Nat.fromBitsLE a * Nat.fromBitsLE d * Nat.fromBitsLE b + 1) := by
  simp only [fullBudgetCode, budgetCode_code, sourceBudgetCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem coefficientBudgetCode_code (a d e b b₀ : List Bool) : coefficientBudgetCode a d e b b₀ =
    BinaryNatCode.encode (Nat.fromBitsLE b₀ + Nat.fromBitsLE a * (Nat.fromBitsLE d + 1).size +
      2 * Nat.fromBitsLE a * Nat.fromBitsLE d * (Nat.fromBitsLE b + (Nat.fromBitsLE e + 1).size) + 1) := by
  simp only [coefficientBudgetCode, fullBudgetCode_code, sourceBudgetCode_code, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, show Nat.fromBitsLE [true] = 1 from rfl, Nat.one_mul]

theorem natDegree_le_degreeCode {σ R : Type*} [Fintype σ] [CommSemiring R]
    (p : MvPolynomial σ R) (n d : σ → R[X]) (a D E : List Bool)
    (hcard : Fintype.card σ ≤ Nat.fromBitsLE a) (hD : ∀ i, p.degreeOf i ≤ Nat.fromBitsLE D)
    (hn : ∀ i, (n i).natDegree ≤ Nat.fromBitsLE E) (hd : ∀ i, (d i).natDegree ≤ Nat.fromBitsLE E) :
    (cleared p n d).natDegree ≤ Nat.fromBitsLE (degreeCode a D E) := by
  rw [degreeCode_code, show Nat.fromBitsLE (BinaryNatCode.encode
    (2 * Nat.fromBitsLE a * Nat.fromBitsLE D * Nat.fromBitsLE E)) =
    2 * Nat.fromBitsLE a * Nat.fromBitsLE D * Nat.fromBitsLE E from Nat.fromBitsLE_bits _]
  exact (natDegree_cleared_le_uniform p n d _ _ hD hn hd).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hcard)))

theorem coeff_size_le_budgetCode {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℤ) (n d : σ → ℤ[X]) (a D b s : List Bool)
    (hcard : Fintype.card σ ≤ Nat.fromBitsLE a) (hD : ∀ i, p.degreeOf i ≤ Nat.fromBitsLE D)
    (hp : sourceMass p ≤ 2 ^ Nat.fromBitsLE s)
    (hn : ∀ i, coefficientMass (n i) ≤ 2 ^ Nat.fromBitsLE b)
    (hd : ∀ i, coefficientMass (d i) ≤ 2 ^ Nat.fromBitsLE b) (k : ℕ) :
    ((cleared p n d).coeff k).natAbs.size ≤ Nat.fromBitsLE (budgetCode a D b s) := by
  simp only [budgetCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  apply (coeff_size_cleared_le_uniform p n d _ _ _ hp hD hn hd k).trans
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hcard))) _) 1

theorem coeff_size_le_fullBudgetCode {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℤ) (n d : σ → ℤ[X]) (a D b b₀ : List Bool)
    (hcard : Fintype.card σ ≤ Nat.fromBitsLE a) (hD : ∀ i, p.degreeOf i ≤ Nat.fromBitsLE D)
    (h₀ : ∀ e, (p.coeff e).natAbs ≤ 2 ^ Nat.fromBitsLE b₀)
    (hn : ∀ i, coefficientMass (n i) ≤ 2 ^ Nat.fromBitsLE b)
    (hd : ∀ i, coefficientMass (d i) ≤ 2 ^ Nat.fromBitsLE b) (k : ℕ) :
    ((cleared p n d).coeff k).natAbs.size ≤ Nat.fromBitsLE (fullBudgetCode a D b b₀) := by
  apply coeff_size_le_budgetCode p n d a D b (sourceBudgetCode a D b₀) hcard hD ?_ hn hd k
  simp only [sourceBudgetCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact (sourceMass_le_pow_uniform p _ _ hD h₀).trans (Nat.pow_le_pow_right (by decide)
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ hcard) _))

theorem coeff_size_le_coefficientBudgetCode {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℤ) (n d : σ → ℤ[X]) (a D E b b₀ : List Bool)
    (hcard : Fintype.card σ ≤ Nat.fromBitsLE a) (hD : ∀ i, p.degreeOf i ≤ Nat.fromBitsLE D)
    (h₀ : ∀ e, (p.coeff e).natAbs ≤ 2 ^ Nat.fromBitsLE b₀)
    (hnD : ∀ i, (n i).natDegree ≤ Nat.fromBitsLE E) (hdD : ∀ i, (d i).natDegree ≤ Nat.fromBitsLE E)
    (hn : ∀ i k, ((n i).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE b)
    (hd : ∀ i k, ((d i).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE b) (k : ℕ) :
    ((cleared p n d).coeff k).natAbs.size ≤ Nat.fromBitsLE (coefficientBudgetCode a D E b b₀) := by
  apply coeff_size_le_fullBudgetCode p n d a D (sourceBudgetCode [true] E b) b₀ hcard hD h₀ ?_ ?_ k
  · intro i
    simpa only [sourceBudgetCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      show Nat.fromBitsLE [true] = 1 from rfl, Nat.one_mul] using
      coefficientMass_le_pow_of_degree_coeff (n i) _ _ (hnD i) (hn i)
  · intro i
    simpa only [sourceBudgetCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      show Nat.fromBitsLE [true] = 1 from rfl, Nat.one_mul] using
      coefficientMass_le_pow_of_degree_coeff (d i) _ _ (hdD i) (hd i)

end LeanCanny.Algebra.RationalSubstitution
