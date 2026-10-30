/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthBlockRenameSpace
public import LeanCanny.Algebra.FixedWidthRowArithmetic

/-! # Native row readers after embedding in a larger variable block

The original row's coefficient program sees the same context, width, and
modulus. Only its exponent word is repacked, with a native support guard.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthBlockRowBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def source (A W : List Bool → ℕ)
    (p : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ) (modulus : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthRowBits.value (A ∘ pairFst) (W ∘ pairFst) (fun q => p (pairFst q)) pairSnd (modulus ∘ pairFst)

theorem source_packet (A W : List Bool → ℕ)
    (p : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ) (modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    source A W p modulus (pair c (BinaryNatCode.encode r)) = residueBits
      (((p c).coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W c) r) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  let read (c : List Bool) (r : ℕ) := residueBits
    (((p c).coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W c) r) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus c) + 1))
  change read (pairFst (pair c (BinaryNatCode.encode r))) (Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode r)))) = read c r
  simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem evaluator {A N O W : List Bool → ℕ} (hA : UnaryFn A) (hN : UnaryFn N) (hO : UnaryFn O) (hW : UnaryFn W)
    (hfit : ∀ c, O c + A c ≤ N c)
    (p : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ) (target modulus : List Bool → List Bool) (ht : target ∈ FP)
    (P : SpaceFunction (source A W p modulus)) :
    SpaceFunction (FixedWidthRowBits.value N W
      (fun c => MvPolynomial.rename (BlockRenameCoefficient.shift (A c) (N c) (O c) (hfit c)) (p c)) target modulus) := by
  have H := FixedWidthBlockRenameBits.evaluator A N O W target P hA hN hO hW ht
  refine H.congr (funext fun c => ?_)
  exact FixedWidthBlockRenameBits.packet A N O W target (p c) (hfit c) (source A W p modulus) c
    (Nat.fromBitsLE (modulus c) + 1) rfl rfl rfl (source_packet A W p modulus c)

end LeanCanny.Algebra.FixedWidthBlockRowBits
