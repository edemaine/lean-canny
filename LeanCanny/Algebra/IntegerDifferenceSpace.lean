/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerSumSpace

/-! # Native subtraction of signed integer outputs -/

@[expose] public section
namespace LeanCanny.Algebra.IntegerDifferenceBits
open LeanCanny.Encoding LeanCanny.Computation

def value (q : List Bool) : List Bool := IntegerSumBits.difference
  (pair (BinaryNat.add (pair (pairFst (pairFst q)) (pairSnd (pairSnd q))))
    (BinaryNat.add (pair (pairSnd (pairFst q)) (pairFst (pairSnd q)))))

theorem value_FP : value ∈ FP := by
  have pp := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have pn := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have np := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have nn := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hp := mem_FP_comp (mem_FP_pair pp nn) BinaryNat.add_mem_FP
  have hn := mem_FP_comp (mem_FP_pair pn np) BinaryNat.add_mem_FP
  have H := mem_FP_comp (mem_FP_pair hp hn) IntegerSumBits.difference_mem_FP
  exact mem_FP_of_eq H (fun _ => rfl)

theorem value_codes (x y : ℤ) :
    value (pair (SignStatisticBits.integerCode x) (SignStatisticBits.integerCode y)) =
      SignStatisticBits.integerCode (x - y) := by
  simp only [value, SignStatisticBits.integerCode, pairFst_pair, pairSnd_pair,
    BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [show IntegerSumBits.difference (pair (x.toNat + (-y).toNat).bits ((-x).toNat + y.toNat).bits) =
    SignStatisticBits.integerCode (((x.toNat + (-y).toNat : ℕ) : ℤ) - ((-x).toNat + y.toNat)) from
      IntegerSumBits.difference_parts _ _]
  change SignStatisticBits.integerCode _ = SignStatisticBits.integerCode (x - y)
  congr 1
  omega

theorem evaluator {f g : List Bool → ℤ}
    (F : SpaceFunction (fun c => SignStatisticBits.integerCode (f c)))
    (G : SpaceFunction (fun c => SignStatisticBits.integerCode (g c))) :
    SpaceFunction (fun c => SignStatisticBits.integerCode (f c - g c)) :=
  ((F.pairOutputs G).postcompose value value_FP).congr
    (funext fun c => value_codes (f c) (g c))

end LeanCanny.Algebra.IntegerDifferenceBits
