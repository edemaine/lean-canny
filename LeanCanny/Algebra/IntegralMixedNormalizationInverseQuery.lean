/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeIndex
/-! # An exact trailing index selects a later characteristic coefficient

The second request restores the caller modulus and preserves the original
matrix key. Its coefficient index fits the existing quadratic factor cap.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

def inverseIndex (P : Parameters) (z : List Bool) : ℕ :=
  get P .target (pairFst z) + 1 + Nat.fromBitsLE (pairSnd z)

def inverseTask (P : Parameters) :=
  IntegralMixedNormalizationFieldBits.query P pairFst .productPower
    (fun z => modulus P (pairFst z)) (inverseIndex P)

theorem inverseTask_FP (P : Parameters) (a : Access P) : inverseTask P ∈ FP := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  have HT : BinaryFn (fun z => get P .target (pairFst z)) := (get_binary P a .target).comp pairFst_mem_FP
  exact IntegralMixedNormalizationFieldBits.query_FP P a pairFst pairFst_mem_FP .productPower _ _ HM
    ((HT.add (BinaryFn.const 1)).add (BinaryFn.fromBits pairSnd_mem_FP))

theorem inverseIndex_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hk : get P .target q ≤ matrixDimension P F q) :
    inverseIndex P (pair q (BinaryNatCode.encode
      (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree)) ≤
        numericCap P (RankedHistoryTask.root q) := by
  have HT := (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree_le_natDegree
  rw [characteristic_natDegree] at HT
  have HC := factor_cap P F g q hv
  change ((matrixDimension P F q + 1) * (matrixDimension P F q + 1)) * 1 ≤ _ at HC
  simp only [inverseIndex, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HB : get P .target q + 1 + (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree ≤
      ((matrixDimension P F q + 1) * (matrixDimension P F q + 1)) * 1 := by nlinarith
  exact HB.trans HC

theorem inverseTask_reply (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : CharacteristicMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 5)
    (hk : get P .target q ≤ matrixDimension P F q) :
    answer (inverseTask P (pair q (BinaryNatCode.encode
      (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree))) =
      residueBits (((top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.coeff
        (get P .target q + 1 + (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree) : ℤ) :
          ZMod (modulus P q)) := by
  let z := pair q (BinaryNatCode.encode (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree)
  let c := inverseTask P z
  have HZ : pairFst z = q := pairFst_pair _ _
  have HV : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid c inverseTask
    rw [IntegralMixedNormalizationFieldBits.query_birth, IntegralMixedNormalizationFieldBits.query_root, HZ]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P c = 5 := by
    unfold c inverseTask
    rw [IntegralMixedNormalizationFieldBits.query_routine, HZ]
    exact hr
  have HP : isPhase .productPower c := IntegralMixedNormalizationFieldBits.query_phase P pairFst .productPower _ _ z
  have HM : modulus P (pairFst z) ≤ numericCap P (RankedHistoryTask.root (pairFst z)) :=
    IntegralCriticalHistoryEvaluator.modulus_le P _
  have HK : inverseIndex P z ≤ numericCap P (RankedHistoryTask.root (pairFst z)) := by
    rw [HZ]
    exact inverseIndex_cap P F g q hv hk
  have HE := IntegralMixedNormalizationFieldBits.coefficient_value P F pairFst .productPower
    (fun z => modulus P (pairFst z)) (inverseIndex P) z HM (Nat.pos_of_ne_zero (modulus_ne_zero P _)) HK
  have HI : inverseIndex P z = get P .target q + 1 +
      (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree := by
    simp only [inverseIndex, z, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [HZ, HI] at HE
  exact (hx c HV HR HP).trans HE

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
