/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthCriticalSpace
public import LeanCanny.Algebra.ModularPowFP
public import LeanCanny.Encoding.BinaryPowModFP

/-! # Native coefficients after clearing a dyadic level denominator

From coefficients of p, one source call and modular arithmetic give the
coefficients of 2^E p - 1. The exponent E is binary, and the zero-monomial
guard inspects exactly the retained exponent blocks, including width zero.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthDyadicScaleBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical

variable (A W E : List Bool → ℕ) (target modulus : List Bool → List Bool)

def factor (c : List Bool) : List Bool :=
  BinaryNat.powMod (pair (BinaryNatCode.encode 2) (pair (BinaryNatCode.encode (E c))
    (BinaryNat.sub (pair (modulus c) (BinaryNatCode.encode 1)))))

theorem factor_mem_FP (hE : BinaryFn E) (hm : modulus ∈ FP) : factor E modulus ∈ FP := by
  have hsub := mem_FP_comp (mem_FP_pair hm (constFn_mem_FP (BinaryNatCode.encode 1))) BinaryNat.sub_mem_FP
  exact mem_FP_comp (mem_FP_pair (constFn_mem_FP _) (mem_FP_pair hE.bits_mem_FP hsub)) BinaryNat.powMod_mem_FP

noncomputable def correction (c : List Bool) : List Bool :=
  if FixedWidthQuery.Bounded A W target (fun _ => 0) c then
    ArithmeticBits.negate (pair (modulus c)
      (BinaryNat.mod (pair (BinaryNatCode.encode 1) (modulus c))))
  else []

theorem correction_mem_FP (hA : UnaryFn A) (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    correction A W target modulus ∈ FP := by
  have hmod := mem_FP_comp (mem_FP_pair (constFn_mem_FP (BinaryNatCode.encode 1)) hm) BinaryNat.mod_mem_FP
  have hn := mem_FP_comp (mem_FP_pair hm hmod) ArithmeticBits.negate_mem_FP
  have h := (FixedWidthQuery.bounded_fppred hA hW (UnaryFn.const 0) ht).ite_mem_FP hn (constFn_mem_FP [])
  apply mem_FP_of_eq h
  intro c
  simp only [correction, Function.comp_apply]

noncomputable def finish (z : List Bool) : List Bool := ArithmeticBits.addMod
  (pair (modulus (pairFst z)) (pair
    (BinaryNat.mulMod (pair (modulus (pairFst z))
      (pair (pairSnd z) (factor E modulus (pairFst z)))))
    (correction A W target modulus (pairFst z))))

theorem finish_mem_FP (hA : UnaryFn A) (hW : UnaryFn W) (hE : BinaryFn E)
    (ht : target ∈ FP) (hm : modulus ∈ FP) : finish A W E target modulus ∈ FP := by
  have hmod := mem_FP_comp pairFst_mem_FP hm
  have hfactor := mem_FP_comp pairFst_mem_FP (factor_mem_FP E modulus hE hm)
  have hmul := mem_FP_comp (mem_FP_pair hmod (mem_FP_pair pairSnd_mem_FP hfactor)) BinaryNat.mulMod_mem_FP
  have hc := mem_FP_comp pairFst_mem_FP (correction_mem_FP A W target modulus hA hW ht hm)
  have h := mem_FP_comp (mem_FP_pair hmod (mem_FP_pair hmul hc)) ArithmeticBits.addMod_mem_FP
  apply mem_FP_of_eq h
  intro z
  simp only [finish, Function.comp_apply]

noncomputable def value (coefficient : List Bool → List Bool) (c : List Bool) : List Bool :=
  finish A W E target modulus (pair c (coefficient (FixedWidthCriticalBits.sourceQuery target c)))

theorem evaluator {coefficient : List Bool → List Bool} (P : SpaceFunction coefficient)
    (hA : UnaryFn A) (hW : UnaryFn W) (hE : BinaryFn E) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value A W E target modulus coefficient) :=
  (((P.precompose (FixedWidthCriticalBits.sourceQuery target)
    (FixedWidthCriticalBits.sourceQuery_mem_FP target ht)).withInput).postcompose
      (finish A W E target modulus) (finish_mem_FP A W E target modulus hA hW hE ht hm)).congr
    (funext fun _ => rfl)

theorem factor_packet (c : List Bool) (m : ℕ) [NeZero m]
    (hm : modulus c = BinaryNatCode.encode m) :
    factor E modulus c = residueBits (((2 ^ E c : ℕ) : ℤ) : ZMod m) := by
  simp only [factor, hm, BinaryNat.powMod_eq_bits, pairFst_pair, pairSnd_pair,
    BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, residueBits, Int.cast_natCast, ZMod.val_natCast]
  rw [Nat.sub_add_cancel (NeZero.one_le)]

theorem packet {σ : Type*} [Fintype σ] {N : ℕ} (f : σ ≃ Fin N)
    (coefficient : List Bool → List Bool) (c : List Bool) (p : MvPolynomial σ ℤ) (m : ℕ) [NeZero m]
    (hA : A c = N) (hm : modulus c = BinaryNatCode.encode m)
    (hp : ∀ r, coefficient (pair c (BinaryNatCode.encode r)) =
      residueBits ((p.coeff (nativeExponent f (W c) r) : ℤ) : ZMod m)) :
    value A W E target modulus coefficient c = residueBits
      (((MvPolynomial.C (2 ^ E c : ℤ) * p - 1).coeff
        (nativeExponent f (W c) (Nat.fromBitsLE (target c))) : ℤ) : ZMod m) := by
  let e := nativeExponent f (W c) (Nat.fromBitsLE (target c))
  have he (i : σ) : e i = FixedWidthQuery.coordinate W target c (f i).val := by
    simp only [e, nativeExponent, Finsupp.coe_equivFunOnFinite_symm,
      entry_eq_digit, FixedWidthQuery.coordinate, BinaryNat.value_take, drop_value]
  have hz : FixedWidthQuery.Bounded A W target (fun _ => 0) c ↔ e = 0 := by
    constructor
    · intro h
      ext i
      exact Nat.eq_zero_of_le_zero (by rw [he]; exact h _ (by rw [hA]; exact (f i).isLt))
    · intro h i hi
      let j : Fin N := ⟨i, by rwa [← hA]⟩
      have hh := congrArg (fun v : σ →₀ ℕ => v (f.symm j)) h
      simpa only [he, Equiv.apply_symm_apply, Finsupp.zero_apply, j] using hh.le
  have hone : BinaryNat.mod (pair (BinaryNatCode.encode 1) (BinaryNatCode.encode m)) =
      residueBits (1 : ZMod m) := by
    simp only [BinaryNat.mod_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, residueBits, ZMod.val_one_eq_one_mod]
  have hc : correction A W target modulus c = residueBits (-((1 : MvPolynomial σ ℤ).coeff e : ZMod m)) := by
    rw [correction, hz]
    split_ifs with h
    · rw [h, MvPolynomial.coeff_one, ite_eq_left rfl, Int.cast_one, hm, hone,
        ArithmeticBits.negate_residueBits]
    · simp only [MvPolynomial.coeff_one, ite_eq_right (Ne.symm h), Int.cast_zero, neg_zero, residueBits, ZMod.val_zero]
      rfl
  have hp' := hp (Nat.fromBitsLE (target c))
  change coefficient (pair c (Nat.fromBitsLE (target c)).bits) = _ at hp'
  rw [value, finish, pairFst_pair, pairSnd_pair, FixedWidthCriticalBits.sourceQuery,
    BinaryNat.normalize_eq_bits, hp', factor_packet E modulus c m hm, hc, hm,
    ArithmeticBits.mulMod_residueBits, ArithmeticBits.addMod_residueBits]
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul, Int.cast_sub, Int.cast_mul]
  simp only [Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat,
    sub_eq_add_neg, mul_comm, e]

end LeanCanny.Algebra.FixedWidthDyadicScaleBits
