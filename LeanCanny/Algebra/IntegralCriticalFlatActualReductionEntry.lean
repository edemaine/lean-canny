/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActualSources
public import LeanCanny.Algebra.IntegralCriticalFlatReductionEntryCorrect
public import LeanCanny.Algebra.IntegralCriticalFlatReductionPowerLocal
public import LeanCanny.Algebra.IntegralCriticalActualCaps
public import LeanCanny.Algebra.IntegralCriticalTotalMatrixSnapshot
/-! # Actual reduction entry values at finite child tasks -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualReductionEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalTotalSnapshotBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalFlatActualSources.relative IntegralCriticalFlatActualSources.reduction characteristic

noncomputable def value (F : Scripts) (q : List Bool) : List Bool :=
  modularReductionEntry F q (get F.toParameters .row q) (get F.toParameters .col q)

def child (F : Scripts) (c : List Bool) (i j : ℕ) : List Bool :=
  IntegralCriticalFlatMatrixQuery.writer F.toParameters .reductionEntry
    (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j)))

theorem finite_value (F : Scripts) (c : List Bool)
    (i j : Fin ((IntegralCriticalFlatActualSources.reduction F).dimension c * (IntegralCriticalFlatActualSources.reduction F).rank c)) :
    modularReductionEntry F c i.val j.val =
      residueBits ((blockMatrix (IntegralCriticalFlatActualSources.reduction F).toSource c i j : ℤ) : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters c)) :=
  congrArg (fun z : ℤ => residueBits (z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters c))) (integerEntry_fin _ i j)

theorem child_value (F : Scripts) (c : List Bool)
    (hv : IntegralCriticalTotalCompanionBits.valid F c)
    (i j : Fin ((IntegralCriticalFlatActualSources.reduction F).dimension c * (IntegralCriticalFlatActualSources.reduction F).rank c)) :
    value F (child F c i.val j.val) =
      residueBits ((blockMatrix (IntegralCriticalFlatActualSources.reduction F).toSource c i j : ℤ) : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters c)) := by
  have HR : RankedHistoryTask.root (child F c i.val j.val) = RankedHistoryTask.root c := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_root F.toParameters .reductionEntry
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HB : birth F.toParameters (child F c i.val j.val) = birth F.toParameters c := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_birth F.toParameters .reductionEntry
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HM : IntegralCriticalHistoryTask.modulus F.toParameters (child F c i.val j.val) = IntegralCriticalHistoryTask.modulus F.toParameters c := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_modulus F.toParameters .reductionEntry
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HI : get F.toParameters .row (child F c i.val j.val) = i.val := by
    have H := IntegralCriticalActualCaps.reduction_block_cap F c hv
    simp only [child, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]
    exact min_eq_left (Nat.le_trans (Nat.le_of_lt i.isLt) H)
  have HJ : get F.toParameters .col (child F c i.val j.val) = j.val := by
    have H := IntegralCriticalActualCaps.reduction_block_cap F c hv
    simp only [child, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, reduceCtorEq, ite_true, ite_false]
    exact min_eq_left (Nat.le_trans (Nat.le_of_lt j.isLt) H)
  rw [value, HI, HJ, modularReductionEntry_invariance F _ c HR HB HM]
  exact finite_value F c i j

attribute [local irreducible] IntegralCriticalFlatActualSources.relativeAccess IntegralCriticalTotalSnapshotBits.modularReductionEntry
  IntegralCriticalTotalSnapshotBits.reductionEntry

theorem program_value_finite (F : Scripts) (h : Controls F) (answer : List Bool → List Bool) (c : List Bool)
    (he : PurePowerReductionBits.request (IntegralPurePowerReductionBits.layout (IntegralCriticalFlatActualSources.relative F))
      (fun z => (IntegralCriticalFlatActualSources.relative F).layout.bound (pairFst z)) (IntegralPurePowerReductionBits.writer (IntegralCriticalFlatActualSources.relative F)
        (IntegralCriticalFlatReductionEntryBits.packet F.toParameters (IntegralCriticalFlatActualSources.relative F) c)) →
      answer (IntegralCriticalFlatLowerQuery.writer F.toParameters
        (IntegralCriticalFlatReductionEntryBits.lowerInput (IntegralCriticalFlatActualSources.relative F)
          (IntegralCriticalFlatReductionEntryBits.packet F.toParameters (IntegralCriticalFlatActualSources.relative F) c))) =
        (relativeAccess F h).low (IntegralCriticalFlatReductionEntryBits.lowerInput (IntegralCriticalFlatActualSources.relative F)
          (IntegralCriticalFlatReductionEntryBits.packet F.toParameters (IntegralCriticalFlatActualSources.relative F) c)))
    (i j : Fin ((IntegralCriticalFlatActualSources.reduction F).dimension c * (IntegralCriticalFlatActualSources.reduction F).rank c))
    (hi : get F.toParameters .row c = i.val) (hj : get F.toParameters .col c = j.val) :
    (IntegralCriticalFlatReductionEntryBits.program F.toParameters (IntegralCriticalFlatActualSources.relative F) (relativeAccess F h)).value answer c = value F c := by
  let := (IntegralCriticalFlatActualSources.relative F).ring c
  have HD : (IntegralCriticalFlatActualSources.reduction F).dimension c * (IntegralCriticalFlatActualSources.reduction F).rank c =
      (IntegralPurePowerActionBits.reductionSource (IntegralCriticalFlatActualSources.relative F)).dimension c *
        (IntegralCriticalFlatActualSources.relative F).rank c := by
    unfold IntegralCriticalFlatActualSources.reduction
    rfl
  let r := Fin.cast HD i
  let t := Fin.cast HD j
  have HE := IntegralCriticalFlatReductionEntryBits.value_block F.toParameters (IntegralCriticalFlatActualSources.relative F) (relativeAccess F h)
    answer c he r t hi hj
  have HM := congrArg (fun m : ℕ => residueBits ((IntegralCoefficientBlocks.blockHom ((IntegralCriticalFlatActualSources.relative F).basis c)
    ((IntegralPurePowerActionBits.reductionSource (IntegralCriticalFlatActualSources.relative F)).dimension c)
    ((IntegralPurePowerActionBits.reductionSource (IntegralCriticalFlatActualSources.relative F)).matrix c) r t : ℤ) : ZMod m)) (relative_modulus F c)
  have HB : IntegralCoefficientBlocks.blockHom ((IntegralCriticalFlatActualSources.relative F).basis c)
      ((IntegralPurePowerActionBits.reductionSource (IntegralCriticalFlatActualSources.relative F)).dimension c)
      ((IntegralPurePowerActionBits.reductionSource (IntegralCriticalFlatActualSources.relative F)).matrix c) r t =
      blockMatrix (IntegralCriticalFlatActualSources.reduction F).toSource c i j := by
    unfold IntegralCriticalFlatActualSources.reduction
    rfl
  have HEM := HE.trans HM
  rw [HB] at HEM
  rw [value, hi, hj]
  exact HEM.trans (finite_value F c i j).symm

end LeanCanny.Algebra.IntegralCriticalFlatActualReductionEntryBits
