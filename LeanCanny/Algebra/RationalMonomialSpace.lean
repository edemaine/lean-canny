/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitutionFactorFP

/-!
# Certified modular coefficients of cleared monomials

FP binary fields give the variable count, block width, selected degree, and
positive modulus through its predecessor. FP exponent access and space-bounded
coordinate coefficient routines determine each indexed factor. The polynomial
product evaluator computes the selected coefficient with every child included.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower
open scoped BigOperators

noncomputable def monomialValue (arity width modulus degree : List Bool → List Bool)
    (e : List Bool → ℕ → ℕ)
    (np dp : (c : List Bool) → ℕ → Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1))) (c : List Bool) : List Bool :=
  residueBits ((∏ i ∈ Finset.range (Nat.fromBitsLE (arity c)),
    np c i ^ e c i * dp c i ^ (Nat.fromBitsLE (width c) - e c i)).coeff (Nat.fromBitsLE (degree c)))

theorem monomialEvaluator {n d : List Bool → List Bool} (N : SpaceFunction n) (D : SpaceFunction d)
    (arity width exponent modulus degree : List Bool → List Bool)
    (ha : arity ∈ FP) (hw : width ∈ FP) (he : exponent ∈ FP) (hm : modulus ∈ FP) (hk : degree ∈ FP)
    (e : List Bool → ℕ → ℕ)
    (np dp : (c : List Bool) → ℕ → Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1)))
    (hbound : ∀ c i, i < Nat.fromBitsLE (arity c) → e c i ≤ Nat.fromBitsLE (width c))
    (hexp : ∀ c i, i < Nat.fromBitsLE (arity c) →
      Nat.fromBitsLE (exponent (pair c (BinaryNatCode.encode i))) = e c i)
    (hn : ∀ c i, i < Nat.fromBitsLE (arity c) → ∀ k,
      n (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) = residueBits ((np c i).coeff k))
    (hd : ∀ c i, i < Nat.fromBitsLE (arity c) → ∀ k,
      d (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) = residueBits ((dp c i).coeff k)) :
    SpaceFunction (monomialValue arity width modulus degree e np dp) := by
  let F : PolynomialProduct.ModularFamily := {
    count := fun c => Nat.fromBitsLE (arity c) * Nat.fromBitsLE (width c)
    modulus := fun c => Nat.fromBitsLE (modulus c) + 1
    degree := fun c => Nat.fromBitsLE (degree c)
    factor := fun c => flatFactor (np c) (dp c) (e c) (Nat.fromBitsLE (width c))
    modulus_ne_zero := fun _ => by omega }
  let a : PolynomialProduct.ModularAccess F := {
    count := BinaryNat.mul ∘ fun c => pair (arity c) (width c)
    modulus := BinaryNat.succ ∘ modulus
    degree := BinaryNat.normalize ∘ degree
    coefficient := FactorBits.value width exponent n d
    count_eq := fun c => by simp only [Function.comp_apply, BinaryNat.mul_pair, BinaryNatCode.encode, F]
    modulus_eq := fun c => by simp only [Function.comp_apply, BinaryNat.succ_eq_bits, BinaryNatCode.encode, F]
    degree_eq := fun c => by simp only [Function.comp_apply, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, F]
    coefficient_eq := fun c j hj k => FactorBits.value_packet width exponent n d c _ _ (e c) (np c) (dp c)
      (hexp c) (hn c) (hd c) j k hj }
  have hcount := mem_FP_comp (mem_FP_pair ha hw) BinaryNat.mul_mem_FP
  have hmod := mem_FP_comp hm BinaryNat.succ_mem_FP
  have hdegree := mem_FP_comp hk BinaryNat.normalize_mem_FP
  have hcontrols : a.ControlsPolyTime := ⟨hcount, hmod, hdegree⟩
  let Q := a.evaluator hcontrols (FactorBits.evaluator N D width exponent hw he)
  refine Q.congr (funext fun c => ?_)
  change residueBits ((∏ j ∈ Finset.range (Nat.fromBitsLE (arity c) * Nat.fromBitsLE (width c)),
    flatFactor (np c) (dp c) (e c) (Nat.fromBitsLE (width c)) j).coeff (Nat.fromBitsLE (degree c))) = _
  rw [prod_flatFactor _ _ _ _ _ (hbound c)]
  rfl

end LeanCanny.Algebra.RationalSubstitution
