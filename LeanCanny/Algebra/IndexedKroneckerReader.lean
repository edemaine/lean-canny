/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BivariateQueryProductSpace

/-! # Native coefficients of Kronecker-encoded indexed coordinates

Binary division and remainder turn a univariate coefficient query into one
original bivariate coefficient query. The same packet format is used by the
streamed rational-substitution engine; its unit denominators are also native.
-/

@[expose] public section
namespace LeanCanny.Algebra.IndexedKroneckerReader
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

def context (z : List Bool) : List Bool := pairFst (pairFst z)
def coordinate (z : List Bool) : List Bool := pairFst (pairSnd (pairFst z))
def degreeWord (z : List Bool) : List Bool := pairSnd (pairSnd (pairFst z))
theorem context_FP : context ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem coordinate_FP : coordinate ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem degreeWord_FP : degreeWord ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

def query (B : List Bool → ℕ) (z : List Bool) : List Bool :=
  pair (pair (pair (context z) (coordinate z)) (pairSnd z))
    (pair (BinaryNat.mod (pair (degreeWord z) (BinaryNatCode.encode (B (context z)))))
      (BinaryNat.div (pair (degreeWord z) (BinaryNatCode.encode (B (context z))))))

theorem query_FP (B : List Bool → ℕ) (hB : BinaryFn B) : query B ∈ FP := by
  have hb : BinaryFn (fun z => B (context z)) := hB.comp context_FP
  have harg := mem_FP_pair degreeWord_FP hb.bits_mem_FP
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair context_FP coordinate_FP) pairSnd_mem_FP)
    (mem_FP_pair (mem_FP_comp harg BinaryNat.mod_mem_FP) (mem_FP_comp harg BinaryNat.div_mem_FP))

noncomputable def value {F : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access F)
    (B : List Bool → ℕ) : List Bool → List Bool := A.reader.coefficient ∘ query B

theorem evaluator {F : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access F)
    (B : List Bool → ℕ) (hB : BinaryFn B) : SpaceFunction (value A B) := A.reader.evaluator.precompose (query B) (query_FP B hB)

set_option backward.isDefEq.respectTransparency false in
theorem packet {F : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access F)
    (B : List Bool → ℕ) (hB : ∀ c, F.parameterDegree c < B c) (c : List Bool) (i k m : ℕ) (hm : 0 < m) :
    value A B (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((PolynomialKronecker.encode (B c) (F.polynomial c i)).coeff k : ℤ) : ZMod m) := by
  have hq : query B (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      pair (pair (pair c (BinaryNatCode.encode i)) (BinaryNatCode.encode (m - 1)))
        (pair (BinaryNatCode.encode (k % B c)) (BinaryNatCode.encode (k / B c))) := by
    simp only [query, context, coordinate, degreeWord, pairFst_pair, pairSnd_pair,
      BinaryNat.mod_pair, BinaryNat.div_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [value, Function.comp_apply, hq, A.reader.coefficient_eq]
  rw [PolynomialKronecker.coefficient_any (B c) ((Nat.zero_le _).trans_lt (hB c))
    (F.polynomial c i) (fun j => (F.coefficient_degree c i j).trans_lt (hB c))]
  exact congrArg₂ (fun (a : ℤ) (n : ℕ) => residueBits (a : ZMod n))
    (by simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
    (by simp only [pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm])

def unitValue (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (degreeWord z) = 0 then ArithmeticBits.one (BinaryNat.succ (pairSnd z)) else []

theorem unitValue_FP : unitValue ∈ FP := by
  have hz := (BinaryFn.fromBits degreeWord_FP).eq (BinaryFn.const 0)
  have hm := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  have ho := mem_FP_comp hm ArithmeticBits.one_mem_FP
  exact hz.ite_mem_FP ho (constFn_mem_FP [])

theorem unit_packet (c : List Bool) (i k m : ℕ) (hm : 0 < m) :
    unitValue (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits ((((1 : ℤ[X]).coeff k : ℤ)) : ZMod m) := by
  simp only [unitValue, degreeWord, pairFst_pair, pairSnd_pair, BinaryNat.succ_eq_bits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
  by_cases hk : k = 0
  · subst k
    simp only [ite_true, Polynomial.coeff_one_zero]
    simpa only [BinaryNatCode.encode, Int.cast_one] using ArithmeticBits.one_residueBits m
  · simp only [hk, ite_false, Polynomial.coeff_one, Int.cast_zero]
    simp [residueBits, BinaryNatCode.encode]

end LeanCanny.Algebra.IndexedKroneckerReader
