/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPolynomialLayout
public import LeanCanny.Algebra.FixedWidthCoordinateBinary
public import LeanCanny.Algebra.FixedWidthDerivativeSpace

/-! # Native coefficients after multiplication by a spatial coordinate

A positive selected exponent is decremented and repacked at the same width.
One original coefficient call suffices. The specification permits any
additive integer extraction, including an old multiplication-matrix entry.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthCoordinateMulBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (A W selected : List Bool → ℕ) (target : List Bool → List Bool)

def lowered (c : List Bool) (i : ℕ) : ℕ :=
  FixedWidthQuery.entry A W target c i - if i = selected c then 1 else 0

def read (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd q) = selected (pairFst q) then
    BinaryNat.sub (pair (FixedWidthQuery.read A W target q) (BinaryNatCode.encode 1))
  else FixedWidthQuery.read A W target q

theorem read_FP (hA : UnaryFn A) (hW : UnaryFn W) (hs : BinaryFn selected) (ht : target ∈ FP) :
    read A W selected target ∈ FP := by
  have HR := FixedWidthQuery.read_mem_FP hA hW ht
  have HP := (BinaryFn.fromBits pairSnd_mem_FP).eq (hs.comp pairFst_mem_FP)
  have HD := mem_FP_comp (mem_FP_pair HR (constFn_mem_FP (BinaryNatCode.encode 1))) BinaryNat.sub_mem_FP
  exact mem_FP_of_eq (HP.ite_mem_FP HD HR) (fun _ => rfl)

theorem read_packet (c : List Bool) (i : ℕ) :
    read A W selected target (pair c (BinaryNatCode.encode i)) =
      BinaryNatCode.encode (lowered A W selected target c i) := by
  simp only [read, pairFst_pair, pairSnd_pair,
    show Nat.fromBitsLE (BinaryNatCode.encode i) = i from Nat.fromBitsLE_bits i, lowered]
  rw [FixedWidthQuery.read_packet]
  split_ifs <;> simp only [BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_zero]

def packed (c : List Bool) : List Bool := FixedWidthNatVector.encode (A c) (W c) (lowered A W selected target c)

theorem packed_FP (hA : UnaryFn A) (hW : UnaryFn W) (hs : BinaryFn selected) (ht : target ∈ FP) :
    packed A W selected target ∈ FP :=
  FixedWidthNatVector.encode_of_coordinate hA hW
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary
    (FixedWidthNatVector.coordinate_of_reader (read_FP A W selected target hA hW hs ht)
      (read_packet A W selected target))

def query (c : List Bool) : List Bool := pair c (BinaryNat.normalize (packed A W selected target c))

theorem query_FP (hA : UnaryFn A) (hW : UnaryFn W) (hs : BinaryFn selected) (ht : target ∈ FP) :
    query A W selected target ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_comp (packed_FP A W selected target hA hW hs ht) BinaryNat.normalize_mem_FP)

def positive (c : List Bool) : Prop :=
  0 < FixedWidthQuery.entry A W target c (selected c)

instance (c : List Bool) : Decidable (positive A W selected target c) := inferInstanceAs (Decidable (0 < _))

theorem positive_fppred (hA : UnaryFn A) (hW : UnaryFn W) (hs : BinaryFn selected) (ht : target ∈ FP) :
    FPPred (positive A W selected target) := by
  have HR := FixedWidthQuery.entry_binary A W target hA hW ht
  have HQ : (fun c => pair c (BinaryNatCode.encode (selected c))) ∈ FP := mem_FP_pair id_mem_FP hs.bits_mem_FP
  have HE : BinaryFn (fun c => FixedWidthQuery.entry A W target c (selected c)) :=
    BinaryFn.of_eq (HR.comp HQ) (fun c => by simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
  exact (BinaryFn.const 0).lt HE

noncomputable def value (coefficient : List Bool → List Bool) (c : List Bool) : List Bool :=
  if positive A W selected target c then coefficient (query A W selected target c) else []

theorem evaluator {coefficient : List Bool → List Bool} (E : SpaceFunction coefficient)
    (hA : UnaryFn A) (hW : UnaryFn W) (hs : BinaryFn selected) (ht : target ∈ FP) :
    SpaceFunction (value A W selected target coefficient) :=
  (SpaceFunction.branch (fun c => decide (positive A W selected target c))
    (positive_fppred A W selected target hA hW hs ht).flag_mem_FP
    (E.precompose (query A W selected target) (query_FP A W selected target hA hW hs ht))
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (funext fun _ => by simp only [value, Function.comp_apply, decide_eq_true_eq])

theorem packed_exponent {σ : Type*} [Fintype σ] {N : ℕ} (f : σ ≃ Fin N)
    (c : List Bool) (base : σ) (hA : A c = N) (hs : selected c = (f base).val) :
    nativeExponent f (W c) (Nat.fromBitsLE (packed A W selected target c)) =
      FixedWidthDerivativeBits.exponent W target f c - Finsupp.single base 1 := by
  ext z
  have HI : (f z).val < A c := by rw [hA]; exact (f z).isLt
  have HB : lowered A W selected target c (f z).val < 2 ^ W c := by
    apply (Nat.sub_le _ _).trans_lt
    rw [FixedWidthQuery.entry, ite_eq_left HI, FixedWidthQuery.coordinate_eq_entry]
    exact entry_lt _ _ _
  have HE : ((f z).val = selected c) ↔ z = base := by
    rw [hs, Fin.val_inj]
    exact f.injective.eq_iff
  simp only [nativeExponent, Finsupp.coe_equivFunOnFinite_symm, entry_eq_digit,
    ← BinaryNat.value_take, ← drop_value, packed]
  rw [FixedWidthNatVector.decode_block _ _ _ _ HI HB]
  simp only [lowered, FixedWidthQuery.entry, HI, ite_true, HE,
    FixedWidthDerivativeBits.exponent, Finsupp.coe_equivFunOnFinite_symm,
    Finsupp.tsub_apply, Finsupp.single_apply, eq_comm]

theorem packet {σ R : Type*} [Fintype σ] [CommSemiring R] {N : ℕ} (f : σ ≃ Fin N)
    (extract : R →+ ℤ) (coefficient : List Bool → List Bool) (c : List Bool)
    (p : MvPolynomial σ R) (base : σ) (m : ℕ) (hA : A c = N) (hs : selected c = (f base).val)
    (hp : ∀ r, coefficient (pair c (BinaryNatCode.encode r)) =
      residueBits ((extract (p.coeff (nativeExponent f (W c) r)) : ℤ) : ZMod m)) :
    value A W selected target coefficient c =
      residueBits ((extract ((MvPolynomial.X base * p).coeff
        (FixedWidthDerivativeBits.exponent W target f c)) : ℤ) : ZMod m) := by
  let e := FixedWidthDerivativeBits.exponent W target f c
  have HE : FixedWidthQuery.entry A W target c (selected c) = e base := by
    rw [FixedWidthQuery.entry, hs, ite_eq_left (by rw [hA]; exact (f base).isLt)]
    rfl
  have HP : positive A W selected target c ↔ base ∈ e.support := by
    rw [positive, HE, Finsupp.mem_support_iff, Nat.pos_iff_ne_zero]
  rw [MvPolynomial.coeff_X_mul']
  by_cases h : base ∈ e.support
  · rw [value, ite_eq_left (HP.mpr h), ite_eq_left h]
    unfold query
    rw [BinaryNat.normalize_eq_bits]
    change coefficient (pair c (BinaryNatCode.encode (Nat.fromBitsLE (packed A W selected target c)))) = _
    rw [hp, packed_exponent A W selected target f c base hA hs]
  · rw [value, ite_eq_right (fun H => h (HP.mp H)), ite_eq_right h, map_zero]
    simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

end LeanCanny.Algebra.FixedWidthCoordinateMulBits
