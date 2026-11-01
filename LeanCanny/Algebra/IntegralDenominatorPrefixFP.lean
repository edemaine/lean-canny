/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralDenominatorPassCorrect

/-! # Native denominator reads at any earlier birth

A binary requested length is clipped to the original unary history count.
The same instruction fields serve every truncated pass; no list or history
is rebuilt. Its integer recurrence is exactly the original recurrence.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralDenominatorPass
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

def truncate (F : Family) (length : List Bool → ℕ) : Family :=
  { F with count := fun c => min (length c) (F.count c) }

theorem Access.truncate (F : Family) (a : Access F) (length : List Bool → ℕ) (hl : BinaryFn length) : Access (truncate F length) where
  count := (UnaryFn.fromBitsLE_min hl.bits_mem_FP a.count).of_eq
    (fun c => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
  modulus := a.modulus
  arity := a.arity
  leading := a.leading
  degree := a.degree
  exponent := a.exponent
  index := a.index

theorem integers_truncate (F : Family) (length : List Bool → ℕ) (c : List Bool) (i : ℕ) :
    integers (truncate F length) c i = integers F c i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [integers, integers, ih]
    rfl

theorem prefix_reader_FP (F : Family) (a : Access F) (length : List Bool → ℕ) (hl : BinaryFn length)
    (j : List Bool → ℕ) (hj : BinaryFn j) :
    (fun c => residueBits (((integers F c (min (length c) (F.count c)))[j c]?).getD 0 : ZMod (F.modulus c))) ∈ FP := by
  have H := integer_reader_FP (truncate F length) (a.truncate F length hl) j hj
  refine mem_FP_of_eq H (fun c => ?_)
  change residueBits (((integers (truncate F length) c (min (length c) (F.count c)))[j c]?).getD 0 : ZMod (F.modulus c)) = _
  rw [integers_truncate]

end LeanCanny.Algebra.IntegralDenominatorPass
