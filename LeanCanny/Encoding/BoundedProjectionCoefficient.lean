/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionLowest
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Native modular coefficients of the actual critical-sample projection polynomial -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets MatrixPower
open scoped Classical
attribute [local irreducible] BoundedProjectionCharacteristic.polynomial BoundedCriticalProjection.polynomial

/-- Input: `pair (pair context modulusPredecessor) coefficientIndex`. -/
noncomputable def value (P : Readers) (q : List Bool) : List Bool :=
  residueBits (((BoundedCriticalProjection.polynomial P (pairFst (pairFst q))).coeff
    (Nat.fromBitsLE (pairSnd q)) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1))

/-- Attach the retained index and the computed characteristic index. -/
def query (z : List Bool) : List Bool :=
  pair (pairFst (pairFst z)) (pair (BinaryNat.normalize (pairSnd (pairFst z))) (pairSnd z))

theorem query_FP : query ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP)
      pairSnd_mem_FP)

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P) := by
  let R := BoundedProjectionCharacteristic.reader h ha
  have E := (BoundedProjectionLowest.index_evaluator h ha).precompose
    (fun q => pairFst (pairFst q)) (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have Q := E.withInput.chain (R.evaluator.precompose query query_FP)
  refine Q.congr (funext fun q => ?_)
  change R.coefficient (query (pair q (BoundedProjectionLowest.index P (pairFst (pairFst q))))) = _
  simp only [query, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, BoundedProjectionLowest.index]
  change R.coefficient (pair (pairFst q) (pair (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q)))
    (BinaryNatCode.encode (BoundedProjectionCharacteristic.polynomial P (pairFst (pairFst q))).natTrailingDegree))) = _
  rw [R.coefficient_eq]
  change residueBits (((BoundedProjectionCharacteristic.polynomial P (pairFst (pairFst q))).trailingCoeff.coeff
    (Nat.fromBitsLE (pairSnd q)) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1)) = _
  rw [BoundedProjectionCharacteristic.lowest_eq]
  rfl

theorem value_packet (P : Readers) (c m : List Bool) (k : ℕ) :
    value P (pair (pair c m) (BinaryNatCode.encode k)) =
      residueBits (((BoundedCriticalProjection.polynomial P c).coeff k : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  generalize hz : pair (pair c m) (BinaryNatCode.encode k) = z
  have hc : pairFst (pairFst z) = c := by rw [← hz, pairFst_pair, pairFst_pair]
  have hm : pairSnd (pairFst z) = m := by rw [← hz, pairFst_pair, pairSnd_pair]
  have hk : Nat.fromBitsLE (pairSnd z) = k := by
    rw [← hz, pairSnd_pair]
    exact Nat.fromBitsLE_bits k
  subst c
  subst m
  subst k
  rfl

end LeanCanny.Encoding.BoundedProjectionCoefficient
