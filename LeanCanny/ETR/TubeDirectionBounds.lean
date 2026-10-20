/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeBivariateSpace
public import LeanCanny.ETR.IndexedExpansionSize

/-! # Direction bounds from the actual encoded integer reader

Summing output lengths over the polynomially many spatial coordinates gives a
unary FP budget. Each direction entry's bit length is bounded by its own encoded
output length, hence by that sum. No separate direction-size oracle is needed.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeBivariate
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open scoped BigOperators

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

noncomputable def directionSize (source read : List Bool → List Bool) (c : List Bool) : ℕ :=
  ∑ i ∈ Finset.range (TubeParameter.spatialCount (source c)), (read (pair c (BinaryNatCode.encode i))).length

theorem directionSize_unary {source read : List Bool → List Bool} (hs : source ∈ FP) (hr : read ∈ FP) :
    UnaryFn (directionSize source read) := by
  have h := (TubeParameter.spatialCount_unary.comp hs).sum (UnaryFn.length (mem_FP_comp MacaulayBits.loopQuery_mem_FP hr))
  exact h.of_eq (fun c => by simp only [directionSize, Function.comp_apply, MacaulayBits.loopQuery,
    pairFst_pair, pairSnd_pair, List.length_replicate])

theorem direction_entry_bits (source read : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (c : List Bool) (i : ℕ) (hi : i < TubeParameter.spatialCount (source c)) :
    (ell c i).natAbs.size ≤ directionSize source read c := by
  have hsize := Codec.integer_natAbs_bitSize_le_size (ell c i)
  have hlen : (Codec.integer (ell c i)).size ≤ (read (pair c (BinaryNatCode.encode i))).length := by
    rw [hr c i hi, Data.length_toBits]
  have hsum : (read (pair c (BinaryNatCode.encode i))).length ≤
      ∑ j ∈ Finset.range (TubeParameter.spatialCount (source c)), (read (pair c (BinaryNatCode.encode j))).length :=
    Finset.single_le_sum (f := fun j => (read (pair c (BinaryNatCode.encode j))).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
  exact (hsize.trans hlen).trans hsum

theorem direction_entry_bound (source read : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (c : List Bool) (i : ℕ) (hi : i < TubeParameter.spatialCount (source c)) :
    (ell c i).natAbs ≤ 2 ^ directionSize source read c :=
  (Nat.size_le.mp (direction_entry_bits source read ell hr c i hi)).le

end LeanCanny.ETR.TubeBivariate
