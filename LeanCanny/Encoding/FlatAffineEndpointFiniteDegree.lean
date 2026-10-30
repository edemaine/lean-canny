/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteRows

/-! # Native binary row degrees for the joint finite midpoint system

The two retained degrees are stored in charged records. Original tower
degrees and all row-index arithmetic remain native metadata.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteDegree
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def rowAt (F : Inputs) (s : List Bool) (i : ℕ) : Fin (FlatAffineEndpointFiniteFrame.arity F s) :=
  ⟨min i (FlatAffineEndpointFiniteFrame.arity F s - 1), by
    have hp : 0 < FlatAffineEndpointFiniteFrame.arity F s := Nat.zero_lt_succ _
    omega⟩

theorem rowAt_val (F : Inputs) (s : List Bool) (i : Fin (FlatAffineEndpointFiniteFrame.arity F s)) : rowAt F s i.val = i := by
  apply Fin.ext
  exact Nat.min_eq_left (by have := i.isLt; omega)

noncomputable def innerRow (F : Inputs) (s : List Bool) (i : Fin (FlatAffineEndpointFiniteFrame.arity F s)) :
    Fin (FlatAffineEndpointRows.arity F (pairFst s)) :=
  ⟨i.val - 1, by
    have hi := i.isLt
    have hn : 0 < FlatAffineEndpointRows.arity F (pairFst s) := Nat.zero_lt_succ _
    change i.val < 1 * FlatAffineEndpointRows.arity F (pairFst s) + 1 at hi
    rw [Nat.one_mul] at hi
    omega⟩

theorem degrees_apply (F : Inputs) (s : List Bool) (i : Fin (FlatAffineEndpointFiniteFrame.arity F s)) :
    FlatAffineEndpointFiniteFrame.degrees F s i = if i.val = 0 then FlatAffineEndpointFiniteFrame.degree s else
      FlatAffineEndpointPreparation.degrees F (pairFst s) (innerRow F s i) := by
  by_cases hz : i.val = 0
  · have hi : i = (⟨0, Nat.zero_lt_succ _⟩ : Fin (FlatAffineEndpointFiniteFrame.arity F s)) := Fin.ext hz
    rw [hi, ite_eq_left (by rfl)]
    rfl
  · rw [ite_eq_right hz]
    have hi : FrozenAffineCopies.block (0 : Fin 1) (innerRow F s i) = i := by
      apply Fin.ext
      change (i.val - 1) + FlatAffineEndpointRows.arity F (pairFst s) * 0 + 1 = i.val
      omega
    calc
      _ = FlatAffineEndpointFiniteFrame.degrees F s (FrozenAffineCopies.block (0 : Fin 1) (innerRow F s i)) :=
        congrArg (FlatAffineEndpointFiniteFrame.degrees F s) hi.symm
      _ = _ := by simp only [FlatAffineEndpointFiniteFrame.degrees, FrozenAffineCopies.degrees, FrozenAffineCopies.block,
        Fin.cons_succ, Equiv.symm_apply_apply]

noncomputable def degree (F : Inputs) (s : List Bool) (i : ℕ) : ℕ :=
  FlatAffineEndpointFiniteFrame.degrees F s (rowAt F s i)

noncomputable def indexRow (F : Inputs) (q : List Bool) : Fin (FlatAffineEndpointFiniteFrame.arity F (pairFst q)) :=
  rowAt F (pairFst q) (Nat.fromBitsLE (pairSnd q))

theorem indexRow_unary {F : Inputs} (h : F.Access) : UnaryFn (fun q => (indexRow F q).val) :=
  UnaryFn.fromBitsLE_min pairSnd_mem_FP (((FlatAffineEndpointFiniteFrame.arity_unary h).comp pairFst_mem_FP).sub (UnaryFn.const 1))

noncomputable def innerIndex (F : Inputs) (q : List Bool) : Fin (FlatAffineEndpointRows.arity F (pairFst (pairFst q))) :=
  innerRow F (pairFst q) (indexRow F q)

theorem innerIndex_unary {F : Inputs} (h : F.Access) : UnaryFn (fun q => (innerIndex F q).val) :=
  (indexRow_unary h).sub (UnaryFn.const 1)

noncomputable def innerQuery (F : Inputs) (q : List Bool) : List Bool :=
  pair (pairFst (pairFst q)) (BinaryNatCode.encode (innerIndex F q).val)

theorem innerQuery_FP {F : Inputs} (h : F.Access) : innerQuery F ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (bits_mem_FP (innerIndex_unary h))

theorem degree_binary {F : Inputs} (h : F.Access) :
    BinaryFn (fun q => degree F (pairFst q) (Nat.fromBitsLE (pairSnd q))) := by
  have E := (FlatAffineEndpointGram.degree_binary h).comp (innerQuery_FP h)
  have D : BinaryFn (fun q => FlatAffineEndpointFiniteFrame.degree (pairFst q)) :=
    FlatAffineEndpointFiniteFrame.degree_binary.comp pairFst_mem_FP
  have Z := (BinaryFn.ofUnary (indexRow_unary h)).eq (BinaryFn.const 0)
  apply BinaryFn.of_eq (BinaryFn.ite Z D E)
  intro q
  simp only [Function.comp_apply, innerQuery, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hd : FlatAffineEndpointGram.degree F (pairFst (pairFst q)) (innerIndex F q).val =
      FlatAffineEndpointPreparation.degrees F (pairFst (pairFst q)) (innerIndex F q) :=
    congrArg (FlatAffineEndpointPreparation.degrees F (pairFst (pairFst q)))
      (FlatAffineEndpointCoefficient.rowAt_val F (pairFst (pairFst q)) (innerIndex F q))
  rw [hd]
  exact (degrees_apply F (pairFst q) (indexRow F q)).symm

end LeanCanny.Encoding.FlatAffineEndpointFiniteDegree
