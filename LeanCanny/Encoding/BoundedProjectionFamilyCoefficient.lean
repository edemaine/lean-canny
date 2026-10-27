/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionFamilyLowest
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Native modular coefficients of the actual critical-sample projection polynomial -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionFamilyCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets MatrixPower
open scoped Classical
attribute [local irreducible] BoundedProjectionFamilyCharacteristic.polynomial BoundedProjectionFamily.polynomial

/-- Input: `pair (pair context modulusPredecessor) coefficientIndex`. -/
noncomputable def value (P : Readers) (record : List Bool → List Bool) (q : List Bool) : List Bool :=
  residueBits (((BoundedProjectionFamily.polynomial P record (pairFst (pairFst q))).coeff
    (Nat.fromBitsLE (pairSnd q)) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1))

/-- Attach the retained index and the computed characteristic index. -/
def query (z : List Bool) : List Bool :=
  pair (pairFst (pairFst z)) (pair (BinaryNat.normalize (pairSnd (pairFst z))) (pairSnd z))

theorem query_FP : query ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP)
      pairSnd_mem_FP)

theorem evaluator {P : Readers} {record : List Bool → List Bool} (h : P.PolyTime) (hr : SpaceFunction record)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P record) := by
  let R := BoundedProjectionFamilyCharacteristic.reader h hr ha
  have E := (BoundedProjectionFamilyLowest.index_evaluator h hr ha).precompose
    (fun q => pairFst (pairFst q)) (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have Q := E.withInput.chain (R.evaluator.precompose query query_FP)
  refine Q.congr (funext fun q => ?_)
  change R.coefficient (query (pair q (BoundedProjectionFamilyLowest.index P record (pairFst (pairFst q))))) = _
  simp only [query, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, BoundedProjectionFamilyLowest.index]
  change R.coefficient (pair (pairFst q) (pair (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q)))
    (BinaryNatCode.encode (BoundedProjectionFamilyCharacteristic.polynomial P record (pairFst (pairFst q))).natTrailingDegree))) = _
  rw [R.coefficient_eq]
  change residueBits (((BoundedProjectionFamilyCharacteristic.polynomial P record (pairFst (pairFst q))).trailingCoeff.coeff
    (Nat.fromBitsLE (pairSnd q)) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1)) = _
  rw [BoundedProjectionFamilyCharacteristic.lowest_eq]
  rfl

theorem value_packet (P : Readers) (record : List Bool → List Bool) (c m : List Bool) (k : ℕ) :
    value P record (pair (pair c m) (BinaryNatCode.encode k)) =
      residueBits (((BoundedProjectionFamily.polynomial P record c).coeff k : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
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

end LeanCanny.Encoding.BoundedProjectionFamilyCoefficient
