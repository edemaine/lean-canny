/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BivariateProductSource
public import LeanCanny.Algebra.ModularSumSpace

/-! # Native bivariate products through two streamed modular convolutions

Both counters and the modulus are binary. Each inner convolution calls only
the two original coefficient readers; the outer convolution streams their
parameter-coefficient sums. No intermediate polynomial is stored.
-/

@[expose] public section
namespace LeanCanny.Algebra.CertifiedPolynomial.BivariateProduct
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators

def innerCount (r : List Bool) : List Bool := BinaryNat.succ (pairFst (pairSnd (pairFst r)))
def outerCount (z : List Bool) : List Bool := BinaryNat.succ (pairSnd (pairSnd z))
theorem innerCount_FP : innerCount ∈ FP := by polytime [innerCount]
theorem outerCount_FP : outerCount ∈ FP := by polytime [outerCount]
theorem innerCount_value (r : List Bool) : Nat.fromBitsLE (innerCount r) = inner (pairFst r) + 1 := by
  simp only [innerCount, inner, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
theorem outerCount_value (z : List Bool) : Nat.fromBitsLE (outerCount z) = outer z + 1 := by
  simp only [outerCount, outer, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]

noncomputable def innerAt (p q : List Bool → (ℤ[X])[X]) (z : List Bool) (k : ℕ) : List Bool :=
  residueBits (∑ l ∈ Finset.range (inner z + 1), summand p q z k l)
noncomputable def innerCode (p q : List Bool → (ℤ[X])[X]) (r : List Bool) : List Bool :=
  innerAt p q (pairFst r) (Nat.fromBitsLE (pairSnd r))

theorem inner_evaluator {p q : List Bool → (ℤ[X])[X]} (A : BivariateReader p) (B : BivariateReader q) :
    SpaceFunction (innerCode p q) := by
  have hm := mem_FP_comp pairFst_mem_FP modulusCode_FP
  have hvalue : (fun r => Nat.fromBitsLE ((modulusCode ∘ pairFst) r)) = fun r => modulus (pairFst r) := by
    funext r
    simp only [Function.comp_apply, modulusCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have E := ModularSum.evaluatorWithModulus (term_evaluator A B) innerCount (modulusCode ∘ pairFst)
    innerCount_FP hm (fun r => modulus (pairFst r)) hvalue
    (fun r l => summand p q (pairFst r) (Nat.fromBitsLE (pairSnd r)) l)
    (by intro r; dsimp [modulus]; omega)
    (by
      intro r l _
      change term A B (pair r (BinaryNatCode.encode l)) = termCode p q (pairFst r) (Nat.fromBitsLE (pairSnd r)) l
      rw [term_eq]
      simp only [request, outerIndex, innerIndex, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
  refine E.congr (funext fun r => ?_)
  rw [innerCount_value]
  rfl

noncomputable def value (p q : List Bool → (ℤ[X])[X]) (z : List Bool) : List Bool :=
  residueBits (∑ k ∈ Finset.range (outer z + 1), ∑ l ∈ Finset.range (inner z + 1), summand p q z k l)

theorem evaluator {p q : List Bool → (ℤ[X])[X]} (A : BivariateReader p) (B : BivariateReader q) :
    SpaceFunction (value p q) := by
  have hvalue : (fun z => Nat.fromBitsLE (modulusCode z)) = modulus := by
    funext z
    simp only [modulusCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have E := ModularSum.evaluatorWithModulus (inner_evaluator A B) outerCount modulusCode
    outerCount_FP modulusCode_FP modulus hvalue
    (fun z k => ∑ l ∈ Finset.range (inner z + 1), summand p q z k l)
    (by intro z; dsimp [modulus]; omega)
    (by
      intro z k _
      change innerCode p q (pair z (BinaryNatCode.encode k)) = innerAt p q z k
      simp only [innerCode, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
  refine E.congr (funext fun z => ?_)
  rw [outerCount_value]
  rfl

theorem product_coefficient (p q : (ℤ[X])[X]) (u v : ℕ) :
    ((p * q).coeff v).coeff u = ∑ k ∈ Finset.range (v + 1), ∑ l ∈ Finset.range (u + 1),
      (p.coeff k).coeff l * (q.coeff (v - k)).coeff (u - l) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem value_eq (p q : List Bool → (ℤ[X])[X]) (z : List Bool) :
    value p q z = residueBits (((((p (origin z) * q (origin z)).coeff (outer z)).coeff (inner z)) : ℤ) : ZMod (modulus z)) := by
  rw [value, product_coefficient]
  simp only [Int.cast_sum, Int.cast_mul, summand]

noncomputable def reader {p q : List Bool → (ℤ[X])[X]} (A : BivariateReader p) (B : BivariateReader q) :
    BivariateReader (fun c => p c * q c) where
  coefficient := value p q
  evaluator := evaluator A B
  coefficient_eq w u v := by
    rw [value_eq]
    exact congrArg₂ (fun (a : ℤ) (n : ℕ) => residueBits (a : ZMod n))
      (by simp only [origin, inner, outer, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
      (by simp only [modulus, pairFst_pair])

end LeanCanny.Algebra.CertifiedPolynomial.BivariateProduct
