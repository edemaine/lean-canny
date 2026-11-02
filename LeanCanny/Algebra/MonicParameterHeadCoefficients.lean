/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MonicParameterRowCoefficients
public import LeanCanny.Algebra.FixedWidthPolynomialLayout
public import LeanCanny.Algebra.UniformIntegralPrefixRows

/-! # Native exponent splitting in the actual newest-first scalar layout

The new scalar is block zero and old scalar blocks follow it. Dropping one
block therefore gives precisely the old exponent query, for every width and
all short or redundant input words.
-/

@[expose] public section
namespace LeanCanny.Algebra.MonicParameterRows
open MvPolynomial FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def headEquiv (m : ℕ) : (Fin m ⊕ Unit) ≃ Fin (m+1) where
  toFun := UniformIntegralPrefixRows.layout m
  invFun := Fin.cases (Sum.inr ()) Sum.inl
  left_inv j := by cases j with
    | inl i => rfl
    | inr u => cases u; rfl
  right_inv i := Fin.cases rfl (fun _=>rfl) i

@[simp] theorem headEquiv_old (m : ℕ) (i : Fin m) : headEquiv m (Sum.inl i)=i.succ := rfl
@[simp] theorem headEquiv_new (m : ℕ) : headEquiv m (Sum.inr ())=0 := rfl

theorem entry_drop_head (W : ℕ) (bits : List Bool) (i : ℕ) :
    entry W (Nat.fromBitsLE (bits.drop W)) i=entry W (Nat.fromBitsLE bits) (i+1) := by
  rw [entry_eq_digit,entry_eq_digit,drop_value,Nat.div_div_eq_div_mul,←pow_add]
  congr 2
  ring

theorem nativeExponent_head (m V : ℕ) (bits : List Bool) :
    nativeExponent (headEquiv m) V (Nat.fromBitsLE bits)=
      appendExponent (nativeExponent (Equiv.refl (Fin m)) V (Nat.fromBitsLE (bits.drop V)))
        (entry V (Nat.fromBitsLE bits) 0) := by
  ext j
  cases j with
  | inl i =>
    rw [appendExponent_old]
    change entry V (Nat.fromBitsLE bits) (i.val+1)=
      entry V (Nat.fromBitsLE (bits.drop V)) i.val
    exact (entry_drop_head V bits i.val).symm
  | inr u =>
    cases u
    rw [appendExponent_new]
    rfl

theorem coefficient_native_head {R : Type*} [CommRing R] {m : ℕ}
    (p : MvPolynomial (Fin m ⊕ Unit) R) (V : ℕ) (bits : List Bool) :
    (rename (headEquiv m) p).coeff (nativeExponent (Equiv.refl (Fin (m+1))) V (Nat.fromBitsLE bits)) =
      p.coeff (appendExponent
        (nativeExponent (Equiv.refl (Fin m)) V (Nat.fromBitsLE (bits.drop V)))
        (entry V (Nat.fromBitsLE bits) 0)) := by
  rw [nativeExponent_refl,coeff_rename_rank,nativeExponent_head]

end LeanCanny.Algebra.MonicParameterRows
