/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalCompanionSource
public import LeanCanny.Algebra.IntegralMixedCoefficientQuery
/-! # Physical companion coefficient requests return to their actual critical source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalUpperBits
set_option backward.isDefEq.respectTransparency false

noncomputable def coefficientTask (P : Parameters) (F : Family) : List Bool → List Bool :=
  IntegralMixedCoefficientQueryBits.writer P .critical .criticalCoefficient ∘ IntegralScalarGeneratorBits.coefficientQuery (scalarFamily P F)

theorem coefficientTask_FP (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) : coefficientTask P F ∈ FP :=
  mem_FP_comp (IntegralScalarGeneratorBits.coefficientQuery_FP (scalarFamily P F) (scalarAccess P a F h))
    (IntegralMixedCoefficientQueryBits.writer_FP P a .critical .criticalCoefficient)

theorem coefficientTask_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 6) :
    IntegralMixedRoutineTaskBits.Frame P q (coefficientTask P F q) := by
  have HP : pairFst (IntegralScalarGeneratorBits.coefficientQuery (scalarFamily P F) q) = q := pairFst_pair _ _
  have HF := IntegralMixedCoefficientQueryBits.writer_frame P .critical .criticalCoefficient
    (IntegralScalarGeneratorBits.coefficientQuery (scalarFamily P F) q) (by rw [HP, hr]; decide)
  simpa only [HP, coefficientTask, Function.comp_apply] using HF

theorem writer_value (P : Parameters) (F : Family) (q : List Bool) (k r t : ℕ)
    (hk : k ≤ numericCap P (RankedHistoryTask.root q))
    (hr : r ≤ numericCap P (RankedHistoryTask.root q)) (ht : t ≤ numericCap P (RankedHistoryTask.root q)) :
    (critical P F).value (IntegralMixedCoefficientQueryBits.writer P .critical .criticalCoefficient
      (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t))))) =
      residueBits (IntegralMixedPhysicalQueryBits.matrixCoefficient F (IntegralMixedPhysicalTaskBits.saved P q)
        (IntegralMixedPhysicalTaskBits.coordinate P q) k r t : ZMod (modulus P q)) := by
  let z := pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))
  let c := IntegralMixedCoefficientQueryBits.writer P .critical .criticalCoefficient z
  have HP : pairFst z = q := pairFst_pair _ _
  have Hfields (f : Field) : get P f c =
      if f = .slot14 then 1 else
      if f = .row then min (Nat.fromBitsLE (IntegralPowerProductBits.rowWord z)) (numericCap P (RankedHistoryTask.root (pairFst z))) else
      if f = .col then min (Nat.fromBitsLE (IntegralPowerProductBits.colWord z)) (numericCap P (RankedHistoryTask.root (pairFst z))) else
      if f = .coefficient then min (Nat.fromBitsLE (IntegralPowerProductBits.factorWord z)) (numericCap P (RankedHistoryTask.root (pairFst z))) else
        get P f (pairFst z) := IntegralMixedCoefficientQueryBits.writer_get P .critical .criticalCoefficient z f
  simp only [z, IntegralPowerProductBits.rowWord, IntegralPowerProductBits.colWord,
    IntegralPowerProductBits.factorWord, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] at Hfields
  have HI : get P .row c = r := by
    simpa only [reduceCtorEq, ite_true, ite_false, min_eq_left hr] using Hfields .row
  have HJ : get P .col c = t := by
    simpa only [reduceCtorEq, ite_true, ite_false, min_eq_left ht] using Hfields .col
  have HK : get P .coefficient c = k := by
    simpa only [reduceCtorEq, ite_true, ite_false, min_eq_left hk] using Hfields .coefficient
  have HC : IntegralMixedPhysicalTaskBits.coordinate P c = IntegralMixedPhysicalTaskBits.coordinate P q := by
    simpa only [IntegralMixedPhysicalTaskBits.coordinate, reduceCtorEq, ite_true, ite_false] using Hfields .slot13
  have HS : IntegralMixedPhysicalTaskBits.saved P c = IntegralMixedPhysicalTaskBits.saved P q := by
    exact (IntegralMixedCoefficientQueryBits.writer_saved P .critical .criticalCoefficient z).trans
      (congrArg (IntegralMixedVirtualTaskBits.saved P) HP)
  have HM : modulus P c = modulus P q :=
    (IntegralMixedCoefficientQueryBits.writer_modulus P .critical .criticalCoefficient z).trans (congrArg (modulus P) HP)
  change (IntegralMixedPhysicalTaskBits.source P F).value c = _
  rw [IntegralMixedPhysicalTaskBits.value_snapshot, HS, HC, HK, HI, HJ, HM]

end LeanCanny.Algebra.IntegralMixedPhysicalCompanionBits
