/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankPolynomialSource
public import LeanCanny.Encoding.FormulaSignSlotRadialBankCenterTest
/-! # Actual integer-source signs on the same full physical sampler tuple -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankPolynomialTest
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation MatrixPower
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedBankSnapshotBits (atKey)
open IntegralFramedBankPolynomialModel (Source Access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (S : Source) (B : Bank) (T : IntegralMixedHeaderTablesBits.Tables)
  (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
  (read refs : List Bool → List Bool)

noncomputable def value := IntegralFramedPhysicalSuffixTest.value B T hr
  (IntegralFramedBankPolynomialSource.source S B read refs)

private theorem column (c d : List Bool)
    (i : Fin ((atKey B.parameters B.plan B.data (B.key c)).count)) :
    IntegralFramedPhysicalSuffixTest.columns B T hr
      (IntegralFramedBankPolynomialSource.source S B read refs) c d i =
        IntegralMixedFramedPhysicalIndex.nativeScalarColumn B.parameters B.plan B.data T hr (B.key c) i := by
  unfold IntegralFramedPhysicalSuffixTest.columns
  apply congrArg (IntegralMixedFramedPhysicalIndex.nativeScalarColumn B.parameters B.plan B.data T hr (B.key c))
  apply Fin.ext
  simp only [IntegralFramedBankPolynomialSource.source, Fin.val_cast, FixedWidthSuffixLiftBits.shift, Nat.zero_add]

theorem packet (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w) :
    value S B T hr read refs (pair (pair c w) d) = InfinitesimalSign.encode
      (SignType.sign ((S.polynomial (read (pair c d))).eval₂ (Int.castRingHom ℝ)
        (fun i => FormulaSignSlotRadialBankCenterTest.center B T hr refs c w hv i.val))) := by
  rw [value, IntegralFramedPhysicalSuffixTest.packet B T hr
    (IntegralFramedBankPolynomialSource.source S B read refs) c w d hv]
  have HC : (fun i => (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hv).val
      (IntegralFramedPhysicalSuffixTest.columns B T hr (IntegralFramedBankPolynomialSource.source S B read refs) c d i)) =
        FormulaSignSlotRadialBankCenterTest.raw B T hr c w hv := by
    funext i
    rw [column S B T hr read refs]
    rfl
  rw [HC]
  exact congrArg InfinitesimalSign.encode
    (IntegralFramedBankPolynomialModel.sign S B read refs c d (FormulaSignSlotRadialBankCenterTest.raw B T hr c w hv))

theorem evaluator (A : Access S) (h : IntegralFramedBankQuery.Access B) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hs : read ∈ FP) (hf : refs ∈ FP)
    (ER : SpaceFunction (SquareSampleInput.rowCoefficient (IntegralFramedPhysicalBankTerm.input B))) :
    SpaceFunction (value S B T hr read refs) :=
  IntegralFramedPhysicalSuffixTest.evaluator B T hr (IntegralFramedBankPolynomialSource.source S B read refs)
    h ht (IntegralFramedBankPolynomialSource.access S A B h read refs hs hf) ER

end LeanCanny.Encoding.IntegralFramedBankPolynomialTest

namespace LeanCanny.Encoding.IntegralFramedMarkedPolynomialTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralFramedBankPolynomialModel (Source Access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (S : Source) {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R) (outer : Bool) (read refs : List Bool → List Bool)

noncomputable def value := IntegralFramedBankPolynomialTest.value S
  (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer) (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR outer)
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR outer) read refs

theorem evaluator (A : Access S) (hs : read ∈ FP) (hf : refs ∈ FP) :
    SpaceFunction (value S hn ht ha hR outer read refs) :=
  IntegralFramedBankPolynomialTest.evaluator S (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer)
    (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR outer) (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR outer)
    read refs A (IntegralMixedPhysicalMarkedPlan.native hn ht ha hR outer)
    (IntegralMixedPhysicalMarkedPlan.tables_native hn ht ha hR outer) hs hf
    (IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha hR outer)

theorem packet (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w) :
    value S hn ht ha hR outer read refs (pair (pair c w) d) = InfinitesimalSign.encode
      (SignType.sign ((S.polynomial (read (pair c d))).eval₂ (Int.castRingHom ℝ)
        (fun i => FormulaSignSlotRadialBankCenterTest.center
          (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer) (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR outer)
          (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR outer) refs c w hv i.val))) :=
  IntegralFramedBankPolynomialTest.packet _ _ _ _ read refs c w d hv

end LeanCanny.Encoding.IntegralFramedMarkedPolynomialTest
