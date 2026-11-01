/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationInverseController
/-! # The normalization scalar is an adaptive characteristic trailing read -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

def leadingTask (P : Parameters) :=
  IntegralMixedNormalizationFieldBits.query P pairFst .productPower
    (fun z => modulus P (pairFst z)) (fun z => Nat.fromBitsLE (pairSnd z))

theorem leadingTask_FP (P : Parameters) (a : Access P) : leadingTask P ∈ FP := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  exact IntegralMixedNormalizationFieldBits.query_FP P a pairFst pairFst_mem_FP .productPower _ _ HM
    (BinaryFn.fromBits pairSnd_mem_FP)

noncomputable def leadingValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits ((IntegralParameterInverse.denominator (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly : ℤ) : ZMod (modulus P q))

theorem leadingValue_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = leadingValue P F q := ⟨_, rfl⟩

theorem leadingTask_reply (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : CharacteristicMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 5) :
    answer (leadingTask P (pair q (BinaryNatCode.encode
      (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree))) = leadingValue P F q := by
  let z := pair q (BinaryNatCode.encode (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree)
  let c := leadingTask P z
  have HZ : pairFst z = q := pairFst_pair _ _
  have HV : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid c leadingTask
    rw [IntegralMixedNormalizationFieldBits.query_birth, IntegralMixedNormalizationFieldBits.query_root, HZ]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P c = 5 := by
    unfold c leadingTask
    rw [IntegralMixedNormalizationFieldBits.query_routine, HZ]
    exact hr
  have HP : isPhase .productPower c := IntegralMixedNormalizationFieldBits.query_phase P pairFst .productPower _ _ z
  have HK : Nat.fromBitsLE (pairSnd z) ≤ numericCap P (RankedHistoryTask.root (pairFst z)) := by
    simp only [z, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have H := (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree_le_natDegree
    rw [characteristic_natDegree] at H
    exact H.trans (dimension_cap P F g q hv)
  have HE := IntegralMixedNormalizationFieldBits.coefficient_value P F pairFst .productPower
    (fun z => modulus P (pairFst z)) (fun z => Nat.fromBitsLE (pairSnd z)) z
    (IntegralCriticalHistoryEvaluator.modulus_le P _) (Nat.pos_of_ne_zero (modulus_ne_zero P _)) HK
  have HI : Nat.fromBitsLE (pairSnd z) = (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree := by
    simp only [z, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [HZ, HI] at HE
  simpa only [leadingValue, IntegralParameterInverse.denominator, Polynomial.trailingCoeff] using (hx c HV HR HP).trans HE

def leadingPost (z : List Bool) : List Bool := pairSnd (pairSnd z)

theorem leadingPost_FP : leadingPost ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

theorem leading_result (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hi : IndexMatches P F answer) (hc : CharacteristicMatches P F answer)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 5) :
    DependentTwoCall.result (indexTask P F) (leadingTask P) leadingPost answer q = leadingValue P F q := by
  unfold DependentTwoCall.result
  rw [indexTask_reply P F g answer hi q hv hr, leadingTask_reply P F g answer hc q hv hr]
  simp only [leadingPost, pairSnd_pair]

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
