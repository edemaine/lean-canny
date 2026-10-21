/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelCardinality

/-! # One FP dyadic exponent for all coordinate projections

Every coordinate direction has one entry equal to one and all other entries
zero. Their encoded direction-size sums coincide, so their nonvanishing
thresholds coincide. A single fixed coordinate reader computes the common
threshold exponent in polynomial time.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDeformation
open LeanCanny.Encoding LeanCanny.Algebra

theorem specializationExponent_congr_directionSize
    (source read₁ read₂ degree bits : List Bool → List Bool) (c : List Bool)
    (h : TubeBivariate.directionSize source read₁ c = TubeBivariate.directionSize source read₂ c) :
    Nat.fromBitsLE (specializationExponent source read₁ degree bits c) =
      Nat.fromBitsLE (specializationExponent source read₂ degree bits c) := by
  simp only [specializationExponent_value, specializationMassCode_value, budget_code,
    TubeBivariate.rowMassCode_value, h]

end LeanCanny.ETR.TubeDeformation

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeProjectionEncoding TubeCompiledAffineRoots
open scoped Classical BigOperators
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCleared.uniformDegree

theorem coordinate_directionSize (c : List Bool) (j : ℕ)
    (hj : j + 1 < TubeParameter.spatialCount (pairFst c)) :
    TubeBivariate.directionSize pairFst (projectionRead (coordinateDirection j)) c =
      (Codec.integer 1).toBits.length +
        (TubeParameter.spatialCount (pairFst c) - 1) * (Codec.integer 0).toBits.length := by
  unfold TubeBivariate.directionSize
  simp_rw [projectionRead_correct]
  rw [← Finset.add_sum_erase (Finset.range (TubeParameter.spatialCount (pairFst c)))
    (fun i => (Codec.integer (coordinateDirection j i)).toBits.length) (Finset.mem_range.mpr hj)]
  simp only [coordinateDirection, ite_true]
  have hs : (∑ i ∈ (Finset.range (TubeParameter.spatialCount (pairFst c))).erase (j + 1),
      (Codec.integer (if i = j + 1 then (1 : ℤ) else 0)).toBits.length) =
        (TubeParameter.spatialCount (pairFst c) - 1) * (Codec.integer 0).toBits.length := by
    calc
      _ = ∑ _i ∈ (Finset.range (TubeParameter.spatialCount (pairFst c))).erase (j + 1),
          (Codec.integer 0).toBits.length := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ite_eq_right (Finset.mem_erase.mp hi).1]
      _ = _ := by simp [Finset.card_erase_of_mem (Finset.mem_range.mpr hj)]
  rw [hs]

theorem coordinate_threshold_eq (c : List Bool)
    (j : Fin (pointCount (TubeIndexed.arity (pairFst c)) + 1)) :
    eliminantThreshold c (coordinateDirection j.val) = eliminantThreshold c (coordinateDirection 0) := by
  have hj : j.val + 1 < TubeParameter.spatialCount (pairFst c) := by
    have hi := j.isLt
    unfold TubeParameter.spatialCount
    omega
  have h0 : 0 + 1 < TubeParameter.spatialCount (pairFst c) := by
    unfold TubeParameter.spatialCount
    omega
  unfold eliminantThreshold
  exact congrArg InfinitesimalSign.dyadic
    (TubeDeformation.specializationExponent_congr_directionSize pairFst
      (projectionRead (coordinateDirection j.val)) (projectionRead (coordinateDirection 0))
      bounds.degree bounds.bits c
      ((coordinate_directionSize c j.val hj).trans (coordinate_directionSize c 0 h0).symm))

theorem coordinateDirectionRead_mem_FP : projectionRead (coordinateDirection 0) ∈ FP := by
  have hlo := BinaryNat.le_fppred pairSnd_mem_FP (constFn_mem_FP [true])
  have hhi := BinaryNat.le_fppred (constFn_mem_FP [true]) pairSnd_mem_FP
  have htest : FPPred (fun q => Nat.fromBitsLE (pairSnd q) = 1) := (hlo.and hhi).of_iff (fun q => by
    change (Nat.fromBitsLE (pairSnd q) ≤ 1 ∧ 1 ≤ Nat.fromBitsLE (pairSnd q)) ↔ _
    exact le_antisymm_iff.symm)
  have he := htest.ite_mem_FP (constFn_mem_FP (Codec.integer 1).toBits) (constFn_mem_FP (Codec.integer 0).toBits)
  apply mem_FP_of_eq he
  intro q
  simp only [projectionRead, coordinateDirection, zero_add]
  split_ifs <;> rfl

noncomputable def coordinateThresholdCode : List Bool → List Bool :=
  TubeDeformation.specializationExponent pairFst (projectionRead (coordinateDirection 0)) bounds.degree bounds.bits

theorem coordinateThresholdCode_mem_FP : coordinateThresholdCode ∈ FP :=
  TubeDeformation.specializationExponent_mem_FP pairFst_mem_FP coordinateDirectionRead_mem_FP bounds.degreeFP bounds.bitsFP

theorem coordinateThreshold_eq_dyadic (c : List Bool) :
    coordinateThreshold c = InfinitesimalSign.dyadic (Nat.fromBitsLE (coordinateThresholdCode c)) := by
  unfold coordinateThreshold
  simp_rw [coordinate_threshold_eq c]
  simp only [Finset.inf'_const]
  rfl

end LeanCanny.ETR.TubeLevelPacket
