/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PseudoRemainderBounds
public import LeanCanny.Algebra.RationalSubstitutionBudget

/-! # FP binary magnitude budgets for pseudo-remainder coefficients -/

@[expose] public section

namespace LeanCanny.Algebra.PseudoRemainder
open Polynomial
open LeanCanny.Encoding

def budgetCode (bound headMassBits inputMassBits : List Bool) : List Bool :=
  RationalSubstitution.budgetCode (BinaryNat.succ bound) [true]
    (BinaryNat.succ headMassBits) inputMassBits

theorem budgetCode_mem_FP {bound bp bg : List Bool → List Bool}
    (hD : bound ∈ FP) (hp : bp ∈ FP) (hg : bg ∈ FP) :
    (fun c => budgetCode (bound c) (bp c) (bg c)) ∈ FP := by
  have h := RationalSubstitution.budgetCode_mem_FP (mem_FP_comp hD BinaryNat.succ_mem_FP)
    (constFn_mem_FP [true]) (mem_FP_comp hp BinaryNat.succ_mem_FP) hg
  refine mem_FP_of_eq (g := fun c => budgetCode (bound c) (bp c) (bg c)) h ?_
  intro c
  simp only [budgetCode, Function.comp_apply]

theorem budgetCode_eq (bound bp bg : List Bool) : budgetCode bound bp bg =
    BinaryNatCode.encode (2 * (Nat.fromBitsLE bound + 1) * (Nat.fromBitsLE bp + 1) +
      Nat.fromBitsLE bg + 1) := by
  simp only [budgetCode, RationalSubstitution.budgetCode_code, BinaryNat.succ_eq_bits,
    Nat.fromBitsLE_bits, show Nat.fromBitsLE [true] = 1 from rfl, mul_one]
  congr 1
  omega

def coefficientBudgetCode (bound degree headBits inputBits : List Bool) : List Bool :=
  budgetCode bound (RationalSubstitution.sourceBudgetCode [true] degree headBits)
    (RationalSubstitution.sourceBudgetCode [true] bound inputBits)

theorem coefficientBudgetCode_mem_FP {bound degree bp bg : List Bool → List Bool}
    (hD : bound ∈ FP) (hd : degree ∈ FP) (hp : bp ∈ FP) (hg : bg ∈ FP) :
    (fun c => coefficientBudgetCode (bound c) (degree c) (bp c) (bg c)) ∈ FP :=
  budgetCode_mem_FP hD
    (RationalSubstitution.sourceBudgetCode_mem_FP (constFn_mem_FP [true]) hd hp)
    (RationalSubstitution.sourceBudgetCode_mem_FP (constFn_mem_FP [true]) hD hg)

/-- Original degree and coefficient bounds supply the complete integer output budget. -/
theorem coeff_size_le_coefficientBudgetCode (p g : ℤ[X]) (bound degree bp bg : List Bool)
    (hp : p.natDegree ≤ Nat.fromBitsLE degree) (hg : g.natDegree ≤ Nat.fromBitsLE bound)
    (hpc : ∀ i, (p.coeff i).natAbs ≤ 2 ^ Nat.fromBitsLE bp)
    (hgc : ∀ i, (g.coeff i).natAbs ≤ 2 ^ Nat.fromBitsLE bg) (i : ℕ) :
    (((step p (Nat.fromBitsLE degree))^[2 * (Nat.fromBitsLE bound + 1)] g).coeff i).natAbs.size ≤
      Nat.fromBitsLE (coefficientBudgetCode bound degree bp bg) := by
  simp only [coefficientBudgetCode, budgetCode_eq, RationalSubstitution.sourceBudgetCode_code,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, show Nat.fromBitsLE [true] = 1 from rfl, one_mul]
  exact iterate_coeff_size_le p g _ _ _ _ i
    (coefficientMass_le_pow_of_degree_coeff p _ _ hp hpc)
    (coefficientMass_le_pow_of_degree_coeff g _ _ hg hgc)

end LeanCanny.Algebra.PseudoRemainder
