/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthLinearCoefficientSpace

/-! # Native constant-row coefficients

A bounded zero-exponent test guards the charged signed scalar reader. This
includes empty variable sets, zero-width exponent layouts, and modulus one.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthConstantBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def value (A W : List Bool → ℕ) (a : List Bool → ℤ)
    (target modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits (((C (a c) : MvPolynomial (Fin (A c)) ℤ).coeff
    (nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c))) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus c) + 1))

theorem zero_iff (A W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) :
    FixedWidthQuery.Bounded A W target (fun _ => 0) c ↔
      nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c)) = 0 := by
  have hv (i : Fin (A c)) : nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c)) i =
      FixedWidthQuery.coordinate W target c i.val := FixedWidthBlockRenameBits.entry_bits _ _ _
  constructor
  · intro h
    ext i
    rw [hv]
    exact Nat.eq_zero_of_le_zero (h i.val i.isLt)
  · intro h i hi
    have he := congrArg (fun e : Fin (A c) →₀ ℕ => e ⟨i, hi⟩) h
    exact (show FixedWidthQuery.coordinate W target c i = 0 from by simpa only [hv, Finsupp.zero_apply] using he).le

theorem evaluator {A W : List Bool → ℕ} {target modulus reader : List Bool → List Bool}
    (hA : UnaryFn A) (hW : UnaryFn W) (ht : target ∈ FP) (hr : SpaceFunction reader)
    (a : List Bool → ℤ) (ha : ∀ c, reader c = residueBits ((a c : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))) :
    SpaceFunction (value A W a target modulus) := by
  have hb := FixedWidthQuery.bounded_fppred hA hW (UnaryFn.const 0) ht
  have H := SpaceFunction.branch (fun c => decide (FixedWidthQuery.Bounded A W target (fun _ => 0) c))
    hb.flag_mem_FP hr (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine H.congr (funext fun c => ?_)
  simp only [decide_eq_true_eq, zero_iff, value, coeff_C]
  by_cases he : nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c)) = 0
  · simp only [he, ite_true, ha]
  · simp only [he, ite_false, Ne.symm he, Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode]
    rfl

end LeanCanny.Algebra.FixedWidthConstantBits
