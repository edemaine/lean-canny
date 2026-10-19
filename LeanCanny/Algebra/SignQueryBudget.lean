/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignQueryBounds
public import LeanCanny.Algebra.RationalSubstitutionBudget

/-! # FP binary budget writers for root-sign product queries and scaled counts -/

@[expose] public section

namespace LeanCanny.Algebra.RootSignQueries
open Complexity
open LeanCanny.Encoding
open Polynomial
open scoped Classical

def queryDegreeCode (count degree : List Bool) : List Bool := RationalSubstitution.degreeCode count [true] degree
def queryBudgetCode (count degree bits : List Bool) : List Bool :=
  RationalSubstitution.budgetCode count [true] (RationalSubstitution.sourceBudgetCode [true] degree bits) []
def countBudgetCode (count degree : List Bool) : List Bool :=
  BinaryNat.succ (BinaryNat.add (pair count (BinaryNatCode.encode degree.length)))

theorem queryDegreeCode_mem_FP {count degree : List Bool → List Bool} (hc : count ∈ FP) (hd : degree ∈ FP) :
    (fun c => queryDegreeCode (count c) (degree c)) ∈ FP :=
  RationalSubstitution.degreeCode_mem_FP hc (constFn_mem_FP [true]) hd

theorem queryBudgetCode_mem_FP {count degree bits : List Bool → List Bool}
    (hc : count ∈ FP) (hd : degree ∈ FP) (hb : bits ∈ FP) :
    (fun c => queryBudgetCode (count c) (degree c) (bits c)) ∈ FP :=
  RationalSubstitution.budgetCode_mem_FP hc (constFn_mem_FP [true])
    (RationalSubstitution.sourceBudgetCode_mem_FP (constFn_mem_FP [true]) hd hb) (constFn_mem_FP [])

theorem countBudgetCode_mem_FP {count degree : List Bool → List Bool} (hc : count ∈ FP) (hd : degree ∈ FP) :
    (fun c => countBudgetCode (count c) (degree c)) ∈ FP := by
  have hsize := bits_mem_FP (UnaryFn.length hd)
  have h := mem_FP_comp (mem_FP_comp (mem_FP_pair hc hsize) BinaryNat.add_mem_FP) BinaryNat.succ_mem_FP
  refine mem_FP_of_eq (g := fun c => countBudgetCode (count c) (degree c)) h ?_
  intro c
  simp only [countBudgetCode, Function.comp_apply, BinaryNatCode.encode]

theorem queryDegreeCode_eq (count degree : List Bool) : queryDegreeCode count degree =
    BinaryNatCode.encode (2 * Nat.fromBitsLE count * Nat.fromBitsLE degree) := by
  simp only [queryDegreeCode, RationalSubstitution.degreeCode_code, show Nat.fromBitsLE [true] = 1 from rfl, Nat.mul_one]

theorem queryBudgetCode_eq (count degree bits : List Bool) : queryBudgetCode count degree bits =
    BinaryNatCode.encode (2 * Nat.fromBitsLE count * (Nat.fromBitsLE bits + (Nat.fromBitsLE degree + 1).size) + 1) := by
  simp only [queryBudgetCode, RationalSubstitution.budgetCode_code, RationalSubstitution.sourceBudgetCode_code,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, show Nat.fromBitsLE [true] = 1 from rfl,
    show Nat.fromBitsLE [] = 0 from rfl, Nat.one_mul, Nat.mul_one, Nat.zero_add]

theorem countBudgetCode_eq (count degree : List Bool) : countBudgetCode count degree =
    BinaryNatCode.encode (Nat.fromBitsLE count + degree.length + 1) := by
  simp only [countBudgetCode, BinaryNat.add_pair, BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem natDegree_le_queryDegreeCode {R J : Type*} [CommSemiring R] [Fintype J]
    (Q : J → R[X]) (e : J → Fin 3) (count degree : List Bool)
    (hc : Fintype.card J ≤ Nat.fromBitsLE count) (hd : ∀ i, (Q i).natDegree ≤ Nat.fromBitsLE degree) :
    (queryPolynomial Q e).natDegree ≤ Nat.fromBitsLE (queryDegreeCode count degree) := by
  simp only [queryDegreeCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact (natDegree_queryPolynomial_le Q e _ hd).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hc))

theorem coeff_size_le_queryBudgetCode {J : Type*} [Fintype J]
    (Q : J → ℤ[X]) (e : J → Fin 3) (count degree bits : List Bool)
    (hc : Fintype.card J ≤ Nat.fromBitsLE count) (hd : ∀ i, (Q i).natDegree ≤ Nat.fromBitsLE degree)
    (hb : ∀ i k, ((Q i).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE bits) (k : ℕ) :
    ((queryPolynomial Q e).coeff k).natAbs.size ≤ Nat.fromBitsLE (queryBudgetCode count degree bits) := by
  simp only [queryBudgetCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact (coeff_size_queryPolynomial_le Q e _ _ hd hb k).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hc)) 1)

theorem scaledRootCount_size_le_countBudgetCode {J : Type*} [Fintype J]
    (p : ℝ[X]) (Q : J → ℝ[X]) (σ : J → SignType) (count degree : List Bool)
    (hc : Fintype.card J ≤ Nat.fromBitsLE count) (hd : p.natDegree ≤ Nat.fromBitsLE degree) :
    (scaledRootCount p Q σ).natAbs.size ≤ Nat.fromBitsLE (countBudgetCode count degree) := by
  have h := scaledRootCount_natAbs_size_le p Q σ
  have hdegree : p.natDegree.size ≤ degree.length := Nat.size_le.mpr (hd.trans_lt (Nat.fromBitsLE_lt_pow_length degree))
  simp only [countBudgetCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  omega

end LeanCanny.Algebra.RootSignQueries
