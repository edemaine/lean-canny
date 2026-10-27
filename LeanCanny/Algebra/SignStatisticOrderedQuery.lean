/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignStatisticQuery

/-! # Descending sign statistics over arbitrary ordered coefficient types

Only a native three-way sign reader is used. The coefficients themselves may
belong to an ordered algebraic slice and need no direct machine encoding.
-/

@[expose] public section
namespace LeanCanny.Algebra.SignStatisticBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation PrincipalSubresultant

theorem descendingOrderedEvaluator {R : Type*} [Zero R] [LinearOrder R]
    {f : List Bool → List Bool} (E : SpaceFunction f)
    (degree : List Bool → List Bool) (hd : degree ∈ FP) (a : List Bool → ℕ → R)
    (hsign : ∀ c i, f (pair c (BinaryNatCode.encode i)) = InfinitesimalSign.encode (SignType.sign (a c i))) :
    SpaceFunction (fun c => integerCode (permanencesMinusVariations
      ((List.range (Nat.fromBitsLE (degree c) + 1)).reverse.map (a c)))) := by
  let Q := E.precompose (reverseQuery degree) (reverseQuery_mem_FP hd)
  let b := fun c i => SignType.sign (a c (Nat.fromBitsLE (degree c) - i))
  have hb : ∀ c i, (f ∘ reverseQuery degree) (pair c (BinaryNatCode.encode i)) = InfinitesimalSign.encode (b c i) := by
    intro c i
    simp only [Function.comp_apply, reverseQuery, pairFst_pair, pairSnd_pair, BinaryNat.sub_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact hsign c _
  have H := evaluator Q (BinaryNat.succ ∘ degree) (mem_FP_comp hd BinaryNat.succ_mem_FP) b hb
  refine H.congr (funext fun c => ?_)
  simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
  congr 1
  rw [← descending_range]
  simpa only [List.map_map, Function.comp_def, b] using permanencesMinusVariations_map_sign
    ((List.range (Nat.fromBitsLE (degree c) + 1)).map (fun i => a c (Nat.fromBitsLE (degree c) - i)))

end LeanCanny.Algebra.SignStatisticBits
