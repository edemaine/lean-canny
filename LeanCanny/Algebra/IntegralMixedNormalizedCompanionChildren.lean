/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionSource
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionLeadingCorrect
/-! # Current normalized companion coefficient children use exact finite old labels -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizedCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedNormalizationTopBits
set_option backward.isDefEq.respectTransparency false

noncomputable def coefficientTask (P : Parameters) (F : Family) : List Bool → List Bool :=
  IntegralMixedCoefficientQueryBits.writer P .normalization .eulerSum ∘ IntegralScalarGeneratorBits.coefficientQuery (scalarFamily P F)

theorem coefficientTask_FP (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) : coefficientTask P F ∈ FP :=
  mem_FP_comp (IntegralScalarGeneratorBits.coefficientQuery_FP (scalarFamily P F) (scalarAccess P a F h hd))
    (IntegralMixedCoefficientQueryBits.writer_FP P a .normalization .eulerSum)

theorem coefficientTask_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 6) :
    IntegralMixedRoutineTaskBits.Frame P q (coefficientTask P F q) := by
  have HP : pairFst (IntegralScalarGeneratorBits.coefficientQuery (scalarFamily P F) q) = q := pairFst_pair _ _
  have HF := IntegralMixedCoefficientQueryBits.writer_frame P .normalization .eulerSum
    (IntegralScalarGeneratorBits.coefficientQuery (scalarFamily P F) q) (by rw [HP, hr]; decide)
  simpa only [HP, coefficientTask, Function.comp_apply] using HF

attribute [local irreducible] scalarFamily IntegralMixedCutNormalizedSource.matrix PaddedIntegralGeneratorFinBits.Family.coefficient

theorem writer_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (k : ℕ)
    (hk : k ≤ numericCap P (RankedHistoryTask.root q))
    (r t : Fin (dimension F (IntegralMixedVirtualTaskBits.saved P q))) :
    normalizedValue P F (IntegralMixedCoefficientQueryBits.writer P .normalization .eulerSum
      (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))) =
      residueBits (IntegralMixedCutNormalizedSource.matrix F (IntegralMixedVirtualTaskBits.saved P q) k r t : ZMod (modulus P q)) := by
  let z := pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  let c := IntegralMixedCoefficientQueryBits.writer P .normalization .eulerSum z
  have HP : pairFst z = q := pairFst_pair _ _
  have HR : r.val ≤ numericCap P (RankedHistoryTask.root q) :=
    r.isLt.le.trans (dimension_cap P F g q hv)
  have HT : t.val ≤ numericCap P (RankedHistoryTask.root q) :=
    t.isLt.le.trans (dimension_cap P F g q hv)
  have Hfields (f : Field) : get P f c =
      if f = .slot14 then 5 else
      if f = .row then min (Nat.fromBitsLE (IntegralPowerProductBits.rowWord z)) (numericCap P (RankedHistoryTask.root (pairFst z))) else
      if f = .col then min (Nat.fromBitsLE (IntegralPowerProductBits.colWord z)) (numericCap P (RankedHistoryTask.root (pairFst z))) else
      if f = .coefficient then min (Nat.fromBitsLE (IntegralPowerProductBits.factorWord z)) (numericCap P (RankedHistoryTask.root (pairFst z))) else
        get P f (pairFst z) := IntegralMixedCoefficientQueryBits.writer_get P .normalization .eulerSum z f
  simp only [z, IntegralPowerProductBits.rowWord, IntegralPowerProductBits.colWord,
    IntegralPowerProductBits.factorWord, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] at Hfields
  have HI : get P .row c = r.val := by
    simpa only [reduceCtorEq, ite_true, ite_false, min_eq_left HR] using Hfields .row
  have HJ : get P .col c = t.val := by
    simpa only [reduceCtorEq, ite_true, ite_false, min_eq_left HT] using Hfields .col
  have HK : get P .coefficient c = k := by
    simpa only [reduceCtorEq, ite_true, ite_false, min_eq_left hk] using Hfields .coefficient
  have HS : IntegralMixedVirtualTaskBits.saved P c = IntegralMixedVirtualTaskBits.saved P q :=
    (IntegralMixedCoefficientQueryBits.writer_saved P .normalization .eulerSum z).trans (congrArg (IntegralMixedVirtualTaskBits.saved P) HP)
  have HM : modulus P c = modulus P q :=
    (IntegralMixedCoefficientQueryBits.writer_modulus P .normalization .eulerSum z).trans (congrArg (modulus P) HP)
  change normalizedValue P F c = _
  unfold normalizedValue
  rw [HS, HK, HI, HJ, HM]
  rw [IntegralCriticalTotalSnapshotBits.integerEntry_fin]

end LeanCanny.Algebra.IntegralMixedNormalizedCompanionBits
