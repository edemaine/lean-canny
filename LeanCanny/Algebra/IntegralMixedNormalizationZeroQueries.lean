/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationFieldQuery
public import LeanCanny.Algebra.IntegralMixedNormalizationHeight
public import LeanCanny.Algebra.IntegerZeroRecursiveController
/-! # Charged small-modulus reads of actual normalization coefficients -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

def smallTask (P : Parameters) :=
  IntegralMixedNormalizationFieldBits.query P pairFst .productPower
    (fun z => Nat.fromBitsLE (pairSnd z) + 1) (fun z => get P .coefficient (pairFst z))

theorem smallTask_FP (P : Parameters) (a : Access P) : smallTask P ∈ FP :=
  IntegralMixedNormalizationFieldBits.query_FP P a pairFst pairFst_mem_FP .productPower
    _ _ ((BinaryFn.fromBits pairSnd_mem_FP).add (BinaryFn.const 1)) ((get_binary P a .coefficient).comp pairFst_mem_FP)

abbrev CharacteristicMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 → isPhase .productPower q →
    answer q = (source P F).value q

def rootBudget (P : Parameters) (height : List Bool → ℕ) (q : List Bool) : ℕ :=
  characteristicBudget P height (RankedHistoryTask.root q)

theorem rootBudget_binary (P : Parameters) (a : Access P) (height : List Bool → ℕ) (hh : BinaryFn height) :
    BinaryFn (rootBudget P height) := (characteristicBudget_binary P a height hh).comp RankedHistoryTask.root_FP

theorem small_replies (P : Parameters) (F : Family) (height : List Bool → ℕ)
    (hc : ∀ r, 2 * characteristicBudget P height r + 4 ≤ P.modulusBound r)
    (answer : List Bool → List Bool) (hx : CharacteristicMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 5) :
    ∀ i < 2 * rootBudget P height q + 4, answer (smallTask P (pair q (BinaryNatCode.encode i))) =
      residueBits (((top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.coeff (get P .coefficient q) : ℤ) : ZMod (i + 1)) := by
  intro i hi
  let m := fun z : List Bool => Nat.fromBitsLE (pairSnd z) + 1
  let k := fun z : List Bool => get P .coefficient (pairFst z)
  let z := pair q (BinaryNatCode.encode i)
  let c := smallTask P z
  have HV : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid c smallTask
    rw [IntegralMixedNormalizationFieldBits.query_birth, IntegralMixedNormalizationFieldBits.query_root]
    simpa only [IntegralMixedVirtualCaps.valid, z, pairFst_pair] using hv
  have HR : IntegralMixedRoutineTaskBits.routine P c = 5 := by
    unfold c smallTask
    rw [IntegralMixedNormalizationFieldBits.query_routine]
    simpa only [z, pairFst_pair] using hr
  have HP : isPhase .productPower c := IntegralMixedNormalizationFieldBits.query_phase P pairFst .productPower m k z
  have HM : m z ≤ numericCap P (RankedHistoryTask.root (pairFst z)) := by
    simp only [m, z, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (by omega : i + 1 ≤ 2 * rootBudget P height q + 4).trans (zero_scan_cap P height hc q)
  have HK : k z ≤ numericCap P (RankedHistoryTask.root (pairFst z)) := get_le P .coefficient (pairFst z)
  have HE := IntegralMixedNormalizationFieldBits.coefficient_value P F pairFst .productPower m k z HM
    (by dsimp only [m]; omega) HK
  have HZ : pairFst z = q := pairFst_pair _ _
  have HMval : m z = i + 1 := by simp only [m, z, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HKval : k z = get P .coefficient q := by simp only [k, HZ]
  rw [HMval, HKval, HZ] at HE
  exact (hx c HV HR HP).trans HE

def zeroProgram (P : Parameters) (height : List Bool → ℕ) :=
  IntegerZeroBits.RecursiveStage.program (rootBudget P height) (smallTask P)

theorem zeroProgram_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (height : List Bool → ℕ)
    (hh : ∀ q, IntegralMixedVirtualCaps.valid P q → ∀ i j,
      (top F (IntegralMixedVirtualTaskBits.saved P q) i j).natAbs ≤ 2 ^ height (RankedHistoryTask.root q))
    (hc : ∀ r, 2 * characteristicBudget P height r + 4 ≤ P.modulusBound r)
    (answer : List Bool → List Bool) (hx : CharacteristicMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 5) :
    (zeroProgram P height).value answer q =
      [decide ((top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.coeff (get P .coefficient q) = 0)] :=
  IntegerZeroBits.RecursiveStage.value_at _ _ answer q _ (coefficient_bits P F g height hh q hv _)
    (small_replies P F height hc answer hx q hv hr)

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
