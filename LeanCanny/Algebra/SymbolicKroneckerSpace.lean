/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableEntrySpace
public import LeanCanny.Encoding.BinaryDivFP

/-! # Native coefficients of a Kronecker-encoded bivariate polynomial -/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicKroneckerBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree mValue)
attribute [local irreducible] BinaryNat.div BinaryNat.mod

def query (B : List Bool → ℕ) (q : List Bool) : List Bool :=
  pair (pair (context q) (pairSnd q))
    (pair (BinaryNat.mod (pair (selectedDegree q) (BinaryNatCode.encode (B (context q)))))
      (BinaryNat.div (pair (selectedDegree q) (BinaryNatCode.encode (B (context q))))))

lemma query_FP (B : List Bool → ℕ) (hB : BinaryFn B) : query B ∈ FP := by
  have hb := hB.comp RationalSubstitution.IntegerBits.context_mem_FP
  have h := mem_FP_pair RationalSubstitution.IntegerBits.selectedDegree_mem_FP (BinaryFn.bits_mem_FP hb)
  exact mem_FP_pair (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP)
    (mem_FP_pair (mem_FP_comp h BinaryNat.mod_mem_FP) (mem_FP_comp h BinaryNat.div_mem_FP))

theorem evaluator (p : List Bool → Polynomial (Polynomial ℤ)) (B : List Bool → ℕ)
    (hB : BinaryFn B) (hpos : ∀ c, 0 < B c)
    (hp : ∀ c j, ((p c).coeff j).natDegree < B c)
    (P : SpaceFunction (SymbolicFixedTableEntryBits.coefficient p)) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => PolynomialKronecker.encode (B c) (p c))) := by
  refine (P.precompose (query B) (query_FP B hB)).congr (funext fun q => ?_)
  simp only [Function.comp_apply, SymbolicFixedTableEntryBits.coefficient, query,
    pairFst_pair, pairSnd_pair, BinaryNat.div_pair, BinaryNat.mod_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, PrimitivePairBits.coefficient,
    PolynomialKronecker.coefficient_any (B (context q)) (hpos _) _ (hp _)]
  rfl

end LeanCanny.Algebra.SymbolicKroneckerBits
