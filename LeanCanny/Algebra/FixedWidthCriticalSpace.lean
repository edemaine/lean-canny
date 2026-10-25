/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthDerivativeBinarySpace
public import LeanCanny.Algebra.ModularAddFP
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Native coefficients of spatial critical equations

The base row is the original polynomial. Each other row is the selected
partial minus a binary natural direction entry times the base partial. Two
source derivative calls and modular arithmetic evaluate its coefficient.
Both degree allowances and direction entries stay in binary.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthCriticalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical

variable (A W D base selected : List Bool → ℕ) (target modulus direction : List Bool → List Bool)

def sourceQuery (c : List Bool) : List Bool := pair c (BinaryNat.normalize (target c))

theorem sourceQuery_mem_FP (ht : target ∈ FP) : sourceQuery target ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_comp ht BinaryNat.normalize_mem_FP)

def scaled (z : List Bool) : List Bool := BinaryNat.mulMod
  (pair (modulus (pairFst z)) (pair (pairSnd (pairSnd z)) (direction (pairFst z))))

theorem scaled_mem_FP (hm : modulus ∈ FP) (hv : direction ∈ FP) : scaled modulus direction ∈ FP := by
  have h := mem_FP_pair (mem_FP_comp pairFst_mem_FP hm)
    (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (mem_FP_comp pairFst_mem_FP hv))
  exact mem_FP_comp h BinaryNat.mulMod_mem_FP

def finish (z : List Bool) : List Bool := ArithmeticBits.addMod
  (pair (modulus (pairFst z)) (pair (pairFst (pairSnd z))
    (ArithmeticBits.negate (pair (modulus (pairFst z)) (scaled modulus direction z)))))

theorem finish_mem_FP (hm : modulus ∈ FP) (hv : direction ∈ FP) : finish modulus direction ∈ FP := by
  have hmod : (fun z => modulus (pairFst z)) ∈ FP := mem_FP_comp pairFst_mem_FP hm
  have hscaled : scaled modulus direction ∈ FP := scaled_mem_FP modulus direction hm hv
  have hnegQuery : (fun z => pair (modulus (pairFst z)) (scaled modulus direction z)) ∈ FP :=
    mem_FP_pair (f := fun z => modulus (pairFst z)) (g := scaled modulus direction) hmod hscaled
  have hneg := mem_FP_comp hnegQuery ArithmeticBits.negate_mem_FP
  have hleft := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hq := mem_FP_pair hmod (mem_FP_pair hleft hneg)
  have h := mem_FP_comp hq ArithmeticBits.addMod_mem_FP
  apply mem_FP_of_eq (g := finish modulus direction) h
  intro z
  simp only [Function.comp_apply, finish]

noncomputable def difference (coefficient : List Bool → List Bool) (c : List Bool) : List Bool :=
  finish modulus direction (pair c (pair
    (FixedWidthDerivativeBits.value A W W D selected target modulus coefficient c)
    (FixedWidthDerivativeBits.value A W W D base target modulus coefficient c)))

theorem difference_evaluator {coefficient : List Bool → List Bool} (E : SpaceFunction coefficient)
    (hA : UnaryFn A) (hW : UnaryFn W) (hD : BinaryFn D) (hb : UnaryFn base) (hs : UnaryFn selected)
    (ht : target ∈ FP) (hm : modulus ∈ FP) (hv : direction ∈ FP) :
    SpaceFunction (difference A W D base selected target modulus direction coefficient) := by
  have EL := FixedWidthDerivativeBits.evaluator_binary_degree A W W D selected target modulus E hA hW hW hD hs ht hm
  have ER := FixedWidthDerivativeBits.evaluator_binary_degree A W W D base target modulus E hA hW hW hD hb ht hm
  exact ((EL.pairOutputs ER).withInput.postcompose (finish modulus direction)
    (finish_mem_FP modulus direction hm hv)).congr (funext fun _ => rfl)

noncomputable def value (coefficient : List Bool → List Bool) (c : List Bool) : List Bool :=
  if selected c = base c then coefficient (sourceQuery target c)
  else difference A W D base selected target modulus direction coefficient c

theorem evaluator {coefficient : List Bool → List Bool} (E : SpaceFunction coefficient)
    (hA : UnaryFn A) (hW : UnaryFn W) (hD : BinaryFn D) (hb : UnaryFn base) (hs : UnaryFn selected)
    (ht : target ∈ FP) (hm : modulus ∈ FP) (hv : direction ∈ FP) :
    SpaceFunction (value A W D base selected target modulus direction coefficient) := by
  have EL := E.precompose (sourceQuery target) (sourceQuery_mem_FP target ht)
  have ER := difference_evaluator A W D base selected target modulus direction E hA hW hD hb hs ht hm hv
  have h := SpaceFunction.branch (fun c => decide (selected c = base c)) (FPPred.eq hs hb).flag_mem_FP EL ER
  exact h.congr (funext fun c => by simp only [value, Function.comp_apply, decide_eq_true_eq])

private theorem entry_fromBits (w : ℕ) (bits : List Bool) (i : ℕ) :
    entry w (Nat.fromBitsLE bits) i = Nat.fromBitsLE ((bits.drop (i * w)).take w) := by
  rw [entry_eq_digit, BinaryNat.value_take, drop_value]

theorem exponent_eq_native {σ : Type*} [Fintype σ] {N : ℕ} (f : σ ≃ Fin N) (c : List Bool) :
    FixedWidthDerivativeBits.exponent W target f c =
      nativeExponent f (W c) (Nat.fromBitsLE (target c)) := by
  ext i
  simp only [FixedWidthDerivativeBits.exponent, nativeExponent, Finsupp.coe_equivFunOnFinite_symm,
    FixedWidthQuery.coordinate, entry_fromBits]

theorem packet {σ : Type*} [Fintype σ] [DecidableEq σ] {N : ℕ} (f : σ ≃ Fin N)
    (p : MvPolynomial σ ℤ) (b i : σ) (v m : ℕ) (coefficient : List Bool → List Bool) (c : List Bool)
    (hA : A c = N) (hb : base c = (f b).val) (hi : selected c = (f i).val)
    (hpos : 0 < D c) (hD : p.totalDegree ≤ D c) (hW : D c < 2 ^ W c)
    (hm : modulus c = BinaryNatCode.encode (m + 1)) (hv : direction c = BinaryNatCode.encode v)
    (hcoefficient : ∀ r, coefficient (pair c (BinaryNatCode.encode r)) =
      residueBits ((p.coeff (nativeExponent f (W c) r) : ℤ) : ZMod (m + 1))) :
    value A W D base selected target modulus direction coefficient c = residueBits
      (((if i = b then p else MvPolynomial.pderiv i p - MvPolynomial.C (v : ℤ) * MvPolynomial.pderiv b p).coeff
        (nativeExponent f (W c) (Nat.fromBitsLE (target c))) : ℤ) : ZMod (m + 1)) := by
  have heq : selected c = base c ↔ i = b := by rw [hi, hb, Fin.val_inj]; exact f.injective.eq_iff
  by_cases hib : i = b
  · rw [value, ite_eq_left (heq.mpr hib), ite_eq_left hib]
    simpa only [sourceQuery, BinaryNat.normalize_eq_bits, BinaryNatCode.encode] using
      hcoefficient (Nat.fromBitsLE (target c))
  · have hL := FixedWidthDerivativeBits.packet A W W D selected target modulus f coefficient c p i (m + 1)
      hA hi hpos hD hW hm hcoefficient
    have hR := FixedWidthDerivativeBits.packet A W W D base target modulus f coefficient c p b (m + 1)
      hA hb hpos hD hW hm hcoefficient
    rw [exponent_eq_native] at hL hR
    rw [value, ite_eq_right (fun h => hib (heq.mp h)), ite_eq_right hib, difference,
      finish, scaled, pairFst_pair, pairSnd_pair, pairFst_pair, pairSnd_pair, hL, hR, hm, hv,
      ArithmeticBits.mulMod_nat_residueBits, ArithmeticBits.negate_residueBits, ArithmeticBits.addMod_residueBits,
      MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul]
    simp only [Int.cast_add, Int.cast_neg, Int.cast_mul, Int.cast_natCast, sub_eq_add_neg, mul_comm]

end LeanCanny.Algebra.FixedWidthCriticalBits
