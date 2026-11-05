/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialBankCenterSource
public import LeanCanny.Encoding.IntegralFramedPhysicalSuffixTest
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedNative
/-! # Actual same-word center signs on full marked and outer samplers

The native original controls supply every row and coefficient reader.
The center is the chronological quotient vector selected by the local table.
No homomorphism, separately sampled coordinate or sign oracle is supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialBankCenterTest
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (B : Bank) (T : IntegralMixedHeaderTablesBits.Tables)
  (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
  (read refs : List Bool → List Bool)

noncomputable def value := IntegralFramedPhysicalSuffixTest.value B T hr
  (FormulaSignSlotRadialBankCenterSource.source B read refs)

noncomputable def raw (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w) :
    Fin ((atKey B.parameters B.plan B.data (B.key c)).count) → ℝ := fun i =>
  (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hv).val
    (IntegralMixedFramedPhysicalIndex.nativeScalarColumn B.parameters B.plan B.data T hr (B.key c) i)

noncomputable def center (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w) (i : ℕ) : ℝ :=
  IntegralMixedFramedBankTermSign.point B.parameters B.plan B.data (B.key c) (raw B T hr c w hv)
    (Nat.fromBitsLE (WordList.get (refs c) i))

private theorem column (c d : List Bool)
    (i : Fin ((atKey B.parameters B.plan B.data (B.key c)).count)) :
    IntegralFramedPhysicalSuffixTest.columns B T hr
      (FormulaSignSlotRadialBankCenterSource.source B read refs) c d i =
        IntegralMixedFramedPhysicalIndex.nativeScalarColumn B.parameters B.plan B.data T hr (B.key c) i := by
  unfold IntegralFramedPhysicalSuffixTest.columns
  apply congrArg (IntegralMixedFramedPhysicalIndex.nativeScalarColumn B.parameters B.plan B.data T hr (B.key c))
  apply Fin.ext
  simp only [FormulaSignSlotRadialBankCenterSource.source,
    Fin.val_cast, FixedWidthSuffixLiftBits.shift, Nat.zero_add]

theorem packet (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w) :
    value B T hr read refs (pair (pair c w) d) = InfinitesimalSign.encode
      (SignType.sign ((FormulaSignSlotRadialCenterCoefficientSource.polynomial (read (pair c d))).eval₂
        (Int.castRingHom ℝ) (fun i => center B T hr refs c w hv i.val))) := by
  rw [value, IntegralFramedPhysicalSuffixTest.packet B T hr
    (FormulaSignSlotRadialBankCenterSource.source B read refs) c w d hv]
  have HC : (fun i => (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hv).val
      (IntegralFramedPhysicalSuffixTest.columns B T hr (FormulaSignSlotRadialBankCenterSource.source B read refs) c d i)) =
        raw B T hr c w hv := by
    funext i
    rw [column B T hr read refs]
    rfl
  rw [HC]
  exact congrArg InfinitesimalSign.encode (FormulaSignSlotRadialBankCenterSource.sign B read refs c d (raw B T hr c w hv))

theorem evaluator (h : IntegralFramedBankQuery.Access B) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hs : read ∈ FP) (hf : refs ∈ FP)
    (ER : SpaceFunction (SquareSampleInput.rowCoefficient (IntegralFramedPhysicalBankTerm.input B))) :
    SpaceFunction (value B T hr read refs) :=
  IntegralFramedPhysicalSuffixTest.evaluator B T hr (FormulaSignSlotRadialBankCenterSource.source B read refs)
    h ht (FormulaSignSlotRadialBankCenterSource.access B h read refs hs hf) ER

end LeanCanny.Encoding.FormulaSignSlotRadialBankCenterTest

namespace LeanCanny.Encoding.FormulaSignSlotRadialMarkedCenterTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R) (outer : Bool) (read refs : List Bool → List Bool)

noncomputable def value := FormulaSignSlotRadialBankCenterTest.value
  (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer) (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR outer)
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR outer) read refs

theorem evaluator (hs : read ∈ FP) (hf : refs ∈ FP) : SpaceFunction (value hn ht ha hR outer read refs) :=
  FormulaSignSlotRadialBankCenterTest.evaluator (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer)
    (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR outer) (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR outer)
    read refs (IntegralMixedPhysicalMarkedPlan.native hn ht ha hR outer)
    (IntegralMixedPhysicalMarkedPlan.tables_native hn ht ha hR outer) hs hf
    (IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha hR outer)

theorem packet (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w) :
    value hn ht ha hR outer read refs (pair (pair c w) d) = InfinitesimalSign.encode
      (SignType.sign ((FormulaSignSlotRadialCenterCoefficientSource.polynomial (read (pair c d))).eval₂
        (Int.castRingHom ℝ) (fun i => FormulaSignSlotRadialBankCenterTest.center
          (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer) (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR outer)
          (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR outer) refs c w hv i.val))) :=
  FormulaSignSlotRadialBankCenterTest.packet _ _ _ read refs c w d hv

end LeanCanny.Encoding.FormulaSignSlotRadialMarkedCenterTest
