/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IteratedDerivativeSpace
public import LeanCanny.Algebra.PrimitivePairReaders

/-! # Indexed integer derivatives with the original source context

The derivative order is a binary field of the source record. Coefficient
queries retain that whole record, so native readers can select coordinates
and derivative orders without regenerating the sampled system.
-/

@[expose] public section
namespace LeanCanny.Algebra.IndexedIntegerDerivativeBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (p : List Bool → ℤ[X]) (order : List Bool → List Bool) (c : List Bool) : ℤ[X] :=
  Polynomial.derivative^[Nat.fromBitsLE (order c)] (p c)

def sourceQuery (q : List Bool) : List Bool :=
  pair (pair (RationalSubstitution.IntegerBits.context (pairFst q)) (pairSnd q)) (pairSnd (pairFst q))

theorem sourceQuery_FP : sourceQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (f := pairFst) (g := RationalSubstitution.IntegerBits.context)
      pairFst_mem_FP RationalSubstitution.IntegerBits.context_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

theorem evaluator (p : List Bool → ℤ[X]) (P : SpaceFunction (PrimitivePairBits.coefficient p))
    {order : List Bool → List Bool} (ho : order ∈ FP) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial p order)) := by
  have S := P.precompose sourceQuery sourceQuery_FP
  have hm := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  have hv : (fun q => Nat.fromBitsLE (BinaryNat.succ (pairSnd q))) =
      (fun q => Nat.fromBitsLE (pairSnd q) + 1) := by
    funext q
    simp only [BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
  have E := IteratedDerivativeBits.evaluatorWithModulus S
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP
    (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP ho) hm
    (fun q => Nat.fromBitsLE (pairSnd q) + 1) hv (fun _ => Nat.zero_lt_succ _)
    (fun q => p (RationalSubstitution.IntegerBits.context q)) (by
      intro q i
      simp only [sourceQuery, Function.comp_apply, pairFst_pair, pairSnd_pair, PrimitivePairBits.coefficient,
        RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
        RationalSubstitution.IntegerBits.mValue, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      rfl)
  exact E.congr (funext fun _ => rfl)

end LeanCanny.Algebra.IndexedIntegerDerivativeBits
