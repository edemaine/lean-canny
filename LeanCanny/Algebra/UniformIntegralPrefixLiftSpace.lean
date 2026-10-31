/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UniformIntegralPrefixLift
public import LeanCanny.Algebra.MatrixDigitLiftSpace

/-! # Native entries for elements retained across scalar births

The old matrix reader is reused at quotient ranks. The combined new-digit
radix is computed in binary from the scalar width and number of extensions;
neither the intervening matrices nor their bases are materialized.
-/

@[expose] public section
namespace LeanCanny.Algebra.UniformIntegralPrefixLiftBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial UniformIntegralPrefix
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Family where
  cap : List Bool → ℕ
  width : List Bool → ℕ
  start : List Bool → ℕ
  finish : List Bool → ℕ
  oldPrefix : ∀ c, Prefix (cap c) (2 ^ width c) (start c)
  newPrefix : ∀ c, Prefix (cap c) (2 ^ width c) (finish c)
  chain : ∀ c, Chain (cap c) (width c) (oldPrefix c) (newPrefix c)
  element : ∀ c, (oldPrefix c).carrier
  modulus : List Bool → ℕ
  row : ∀ c, Fin (count (finish c) (width c))
  col : ∀ c, Fin (count (finish c) (width c))

noncomputable def Family.raw (F : Family) : MatrixDigitLiftBits.Family where
  dimension c := count (F.start c) (F.width c)
  radix c := (F.chain c).radix
  modulus := F.modulus
  matrix c := (Algebra.leftMulMatrix (F.oldPrefix c).basis.finBasis (F.element c)).map
    (Int.castRingHom (ZMod (F.modulus c)))
  row c := Fin.cast (F.chain c).dimension_eq (F.row c)
  col c := Fin.cast (F.chain c).dimension_eq (F.col c)

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool :=
  residueBits ((Algebra.leftMulMatrix (F.newPrefix c).basis.finBasis
    ((F.chain c).embed (F.element c)) (F.row c) (F.col c) : ℤ) : ZMod (F.modulus c))

theorem Family.value_eq (F : Family) : F.raw.value = F.value := by
  funext c
  have HM := (F.chain c).matrix (F.element c) (F.row c) (F.col c)
  by_cases h : (F.row c).val % (F.chain c).radix = (F.col c).val % (F.chain c).radix
  · have HF : (F.raw.row c).modNat = (F.raw.col c).modNat := Fin.ext h
    rw [MatrixDigitLiftBits.Family.value, ite_eq_left HF]
    change residueBits ((Algebra.leftMulMatrix (F.oldPrefix c).basis.finBasis
      (F.element c) ((F.chain c).oldIndex (F.row c)) ((F.chain c).oldIndex (F.col c)) : ℤ) : ZMod (F.modulus c)) = _
    exact congrArg (fun z : ℤ => residueBits (z : ZMod (F.modulus c))) (HM.trans (ite_eq_left h)).symm
  · have HF : (F.raw.row c).modNat ≠ (F.raw.col c).modNat := fun H => h (congrArg Fin.val H)
    rw [MatrixDigitLiftBits.Family.value, ite_eq_right HF]
    simpa only [Int.cast_zero, Family.value] using
      congrArg (fun z : ℤ => residueBits (z : ZMod (F.modulus c))) (HM.trans (ite_eq_right h)).symm

structure Access (F : Family) where
  width : UnaryFn F.width
  length : UnaryFn (fun c => (F.chain c).length)
  row : BinaryFn (fun c => (F.row c).val)
  col : BinaryFn (fun c => (F.col c).val)
  entry : List Bool → List Bool
  entry_eq : ∀ c (i j : Fin (count (F.start c) (F.width c))),
    entry (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((Algebra.leftMulMatrix (F.oldPrefix c).basis.finBasis (F.element c) i j : ℤ) : ZMod (F.modulus c))

noncomputable def access (F : Family) (a : Access F) : MatrixDigitLiftBits.Access F.raw where
  radix := ((BinaryFn.const 2).powUnary a.width).powUnary a.length
  row := a.row
  col := a.col
  entry := a.entry
  entry_eq := a.entry_eq

theorem evaluator (F : Family) (a : Access F) (E : SpaceFunction a.entry) : SpaceFunction F.value :=
  (MatrixDigitLiftBits.evaluator F.raw (access F a) E).congr F.value_eq

end LeanCanny.Algebra.UniformIntegralPrefixLiftBits
