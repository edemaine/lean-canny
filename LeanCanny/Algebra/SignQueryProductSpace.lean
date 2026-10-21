/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalMonomialSpace
public import LeanCanny.Algebra.MatrixPowerArithmeticFP

/-!
# Certified coefficient access for sign-query polynomial products

Each query exponent is zero, one, or two. The streamed product evaluator uses
two factors per input polynomial, with unit padding. Binary count, selected
degree, modulus, and exponent access are FP; original polynomial coefficient
access may use polynomial space. No query polynomial is expanded or stored.
-/

@[expose] public section

namespace LeanCanny.Algebra.RootSignQueries

open LeanCanny.Encoding
open LeanCanny.Computation
open LeanCanny.Encoding.Brackets
open MatrixPower
open Polynomial
open scoped BigOperators

def unitCoefficient (modulus : List Bool → List Bool) (p : List Bool) : List Bool :=
  if BinaryNat.normalize (pairSnd (pairSnd p)) = [] then
    ArithmeticBits.one (BinaryNat.succ (modulus (pairFst p))) else []

theorem unitCoefficient_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : unitCoefficient modulus ∈ FP := by
  have hk := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  have hmod := mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) BinaryNat.succ_mem_FP
  have hone := mem_FP_comp hmod ArithmeticBits.one_mem_FP
  have h := (stringEq_fppred hk (constFn_mem_FP [])).ite_mem_FP hone (constFn_mem_FP [])
  refine mem_FP_of_eq (g := unitCoefficient modulus) h ?_
  intro p
  simp only [Function.comp_apply, unitCoefficient]

theorem unitCoefficient_packet (modulus : List Bool → List Bool) (c : List Bool) (i k : ℕ) :
    unitCoefficient modulus (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) =
      residueBits ((1 : Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1))).coeff k) := by
  by_cases hk : k = 0
  · subst k
    simp only [unitCoefficient, pairFst_pair, pairSnd_pair, show BinaryNatCode.encode 0 = [] from rfl,
      BinaryNat.normalize, ↓reduceIte, Polynomial.coeff_one_zero]
    simpa only [BinaryNat.succ_eq_bits, BinaryNatCode.encode] using
      ArithmeticBits.one_residueBits (Nat.fromBitsLE (modulus c) + 1)
  · have hbits : BinaryNat.normalize (BinaryNatCode.encode k) ≠ [] := by
      rw [show BinaryNat.normalize (BinaryNatCode.encode k) = k.bits from BinaryNat.normalize_bits k]
      exact (BinaryNat.bits_eq_nil_iff k).not.mpr hk
    simp only [unitCoefficient, pairSnd_pair, hbits, ↓reduceIte, Polynomial.coeff_one, hk, ↓reduceIte]
    simp [residueBits, BinaryNatCode.encode]

noncomputable def queryProductValue (count modulus degree : List Bool → List Bool)
    (e : List Bool → ℕ → Fin 3)
    (Q : (c : List Bool) → ℕ → Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1))) (c : List Bool) : List Bool :=
  residueBits ((∏ i ∈ Finset.range (Nat.fromBitsLE (count c)), Q c i ^ (e c i).val).coeff (Nat.fromBitsLE (degree c)))

theorem queryProductEvaluator {f : List Bool → List Bool} (F : SpaceFunction f)
    (count exponent modulus degree : List Bool → List Bool)
    (hc : count ∈ FP) (he : exponent ∈ FP) (hm : modulus ∈ FP) (hd : degree ∈ FP)
    (e : List Bool → ℕ → Fin 3)
    (Q : (c : List Bool) → ℕ → Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1)))
    (hexp : ∀ c i, i < Nat.fromBitsLE (count c) →
      Nat.fromBitsLE (exponent (pair c (BinaryNatCode.encode i))) = (e c i).val)
    (hQ : ∀ c i, i < Nat.fromBitsLE (count c) → ∀ k,
      f (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) = residueBits ((Q c i).coeff k)) :
    SpaceFunction (queryProductValue count modulus degree e Q) := by
  let U := SpaceFunction.ofFP (unitCoefficient modulus) (unitCoefficient_mem_FP hm)
  let E := RationalSubstitution.monomialEvaluator F U count (fun _ => [false, true]) exponent modulus degree
    hc (constFn_mem_FP [false, true]) he hm hd (fun c i => (e c i).val) Q (fun _ _ => 1)
    (fun c i _ => by have h := (e c i).isLt; change (e c i).val ≤ 2; omega) hexp hQ
    (fun c i _ k => unitCoefficient_packet modulus c i k)
  refine E.congr (funext fun c => ?_)
  simp only [RationalSubstitution.monomialValue, one_pow, mul_one, queryProductValue]

end LeanCanny.Algebra.RootSignQueries
