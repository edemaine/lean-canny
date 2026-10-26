/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.DerivativeCoefficientSpace
public import LeanCanny.Algebra.ModularProductSpace
public import Mathlib.Data.Nat.Factorial.BigOperators
public import LeanCanny.Algebra.CoefficientMass

/-! # Native coefficients of a binary-indexed iterated derivative

One source call reads coefficient i+k. The factor (i+k)!/i! is a streamed
modular product with a binary counter, so neither the derivative polynomial
nor the factorial nor a unary derivative order is materialized.
-/

@[expose] public section
namespace LeanCanny.Algebra.IteratedDerivativeBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators

def factor (index order modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  BinaryNat.mod (pair (BinaryNat.sub (pair (BinaryNat.add (pair (index (pairFst q)) (order (pairFst q))))
    (pairSnd q))) (modulus (pairFst q)))

theorem factor_FP {index order modulus : List Bool → List Bool}
    (hi : index ∈ FP) (hk : order ∈ FP) (hm : modulus ∈ FP) : factor index order modulus ∈ FP := by
  have hn := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP hi)
  have ho := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP hk)
  have hj := BinaryFn.fromBits pairSnd_mem_FP
  have hmod := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP hm)
  have h := ((hn.add ho).sub hj).mod hmod
  exact mem_FP_of_eq h.bits_mem_FP (fun _ => by
    simp only [factor, Function.comp_apply, BinaryNat.mod_pair, BinaryNat.sub_pair,
      BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])

def sourceInput (index order : List Bool → List Bool) (c : List Bool) : List Bool :=
  pair c (BinaryNat.add (pair (index c) (order c)))

theorem sourceInput_FP {index order : List Bool → List Bool} (hi : index ∈ FP) (hk : order ∈ FP) :
    sourceInput index order ∈ FP := by
  have h := mem_FP_pair id_mem_FP (mem_FP_comp (mem_FP_pair hi hk) BinaryNat.add_mem_FP)
  exact mem_FP_of_eq h (fun _ => by simp only [sourceInput, Function.comp_apply, id_eq])

def finish (modulus : List Bool → List Bool) (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (modulus (pairFst z)) (pair (pairFst (pairSnd z)) (pairSnd (pairSnd z))))

theorem finish_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : finish modulus ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hm)
    (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)))
    BinaryNat.mulMod_mem_FP
  exact mem_FP_of_eq h (fun _ => by simp only [finish, Function.comp_apply])

noncomputable def value (p : List Bool → ℤ[X]) (index order modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits ((((Polynomial.derivative^[Nat.fromBitsLE (order c)] (p c)).coeff (Nat.fromBitsLE (index c))) : ℤ) :
    ZMod (Nat.fromBitsLE (modulus c)))

private theorem raw_mul (m : List Bool) (a b : ZMod (Nat.fromBitsLE m)) :
    BinaryNat.mulMod (pair m (pair (residueBits a) (residueBits b))) = residueBits (a * b) := by
  simp only [BinaryNat.mulMod_pair, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_mul]

def massBudget (D B : ℕ) : ℕ := B + D.size * D + (D + 1).size

theorem massBudget_binary {D B : List Bool → ℕ} (hD : BinaryFn D) (hB : BinaryFn B) :
    BinaryFn (fun c => massBudget (D c) (B c)) :=
  (hB.add (hD.size.mul hD)).add ((hD.add (BinaryFn.const 1)).size)

theorem coefficient_bound (p : ℤ[X]) (D B : ℕ) (hD : p.natDegree ≤ D)
    (hB : ∀ i, (p.coeff i).natAbs ≤ 2 ^ B) (k i : ℕ) :
    ((Polynomial.derivative^[k] p).coeff i).natAbs ≤ 2 ^ (B + D.size * D) := by
  by_cases hi : i + k ≤ D
  · have hk : k ≤ D := by omega
    have hf : (i + k).descFactorial k ≤ 2 ^ (D.size * D) := by
      calc
        _ ≤ (i + k) ^ k := Nat.descFactorial_le_pow _ _
        _ ≤ D ^ k := Nat.pow_le_pow_left hi _
        _ ≤ (2 ^ D.size) ^ k := Nat.pow_le_pow_left (Nat.lt_size_self D).le _
        _ = 2 ^ (D.size * k) := (pow_mul _ _ _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hk)
    rw [Polynomial.coeff_iterate_derivative, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
    exact (Nat.mul_le_mul hf (hB _)).trans_eq (by rw [← pow_add, Nat.add_comm])
  · rw [Polynomial.coeff_iterate_derivative, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      smul_zero, Int.natAbs_zero]
    exact Nat.zero_le _

theorem mass_bound (p : ℤ[X]) (D B : ℕ) (hD : p.natDegree ≤ D)
    (hB : ∀ i, (p.coeff i).natAbs ≤ 2 ^ B) (k : ℕ) :
    coefficientMass (Polynomial.derivative^[k] p) ≤ 2 ^ massBudget D B :=
  coefficientMass_le_pow_of_degree_coeff _ D (B + D.size * D)
    ((Polynomial.natDegree_iterate_derivative _ _).trans ((Nat.sub_le _ _).trans hD))
    (coefficient_bound p D B hD hB k)

theorem evaluator {source index order modulus : List Bool → List Bool} (S : SpaceFunction source)
    (hi : index ∈ FP) (hk : order ∈ FP) (hm : modulus ∈ FP)
    (hpos : ∀ c, 0 < Nat.fromBitsLE (modulus c)) (p : List Bool → ℤ[X])
    (hs : ∀ c i, source (pair c (BinaryNatCode.encode i)) =
      residueBits (((p c).coeff i : ℤ) : ZMod (Nat.fromBitsLE (modulus c)))) :
    SpaceFunction (value p index order modulus) := by
  have F := ModularProduct.evaluator (SpaceFunction.ofFP _ (factor_FP hi hk hm)) order modulus hk hm
    (fun c j => ((Nat.fromBitsLE (index c) + Nat.fromBitsLE (order c) - j : ℕ) : ZMod (Nat.fromBitsLE (modulus c))))
    hpos (by
      intro c j _
      simp only [factor, pairFst_pair, pairSnd_pair, BinaryNat.mod_pair, BinaryNat.sub_pair,
        BinaryNat.add_pair, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_natCast])
  have Q := ((F.pairOutputs (S.precompose (sourceInput index order) (sourceInput_FP hi hk))).withInput).postcompose
    (finish modulus) (finish_FP hm)
  apply Q.congr
  funext c
  simp only [Function.comp_apply, finish, pairFst_pair, pairSnd_pair]
  have hq : sourceInput index order c = pair c (BinaryNatCode.encode
      (Nat.fromBitsLE (index c) + Nat.fromBitsLE (order c))) := by
    simp only [sourceInput, BinaryNat.add_pair, BinaryNatCode.encode]
  rw [hq, hs]
  have hprod : (∏ j ∈ Finset.range (Nat.fromBitsLE (order c)),
      ((Nat.fromBitsLE (index c) + Nat.fromBitsLE (order c) - j : ℕ) : ZMod (Nat.fromBitsLE (modulus c)))) =
      ((Nat.fromBitsLE (index c) + Nat.fromBitsLE (order c)).descFactorial (Nat.fromBitsLE (order c)) :
        ZMod (Nat.fromBitsLE (modulus c))) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  rw [hprod, raw_mul, value, Polynomial.coeff_iterate_derivative]
  simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]

theorem evaluatorWithModulus {source index order modulus : List Bool → List Bool} (S : SpaceFunction source)
    (hi : index ∈ FP) (hk : order ∈ FP) (hm : modulus ∈ FP)
    (m : List Bool → ℕ) (hvalue : (fun c => Nat.fromBitsLE (modulus c)) = m)
    (hpos : ∀ c, 0 < m c) (p : List Bool → ℤ[X])
    (hs : ∀ c i, source (pair c (BinaryNatCode.encode i)) = residueBits (((p c).coeff i : ℤ) : ZMod (m c))) :
    SpaceFunction (fun c => residueBits
      ((((Polynomial.derivative^[Nat.fromBitsLE (order c)] (p c)).coeff (Nat.fromBitsLE (index c))) : ℤ) : ZMod (m c))) := by
  subst m
  exact evaluator S hi hk hm hpos p hs

end LeanCanny.Algebra.IteratedDerivativeBits
