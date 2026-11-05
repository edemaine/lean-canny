/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialBankCenterTest
public import LeanCanny.Encoding.IntegralFramedPhysicalBankTermPoint
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualitySemantics
/-! # A valid chronological center reference reads the actual full-word field

The finite reference must decode inside the bank. Missing table entries are
still decoded as zero; they are not automatically invalid references.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialMarkedCenterField
open LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry LeanCanny.Algebra LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → Term} (hn : UnaryFn n)
  (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R) (refs : List Bool → List Bool)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
local notation "T" => IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false
local notation "H" => IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR false
local notation "S" => IntegralMixedPhysicalMarkedTest.input hn ht ha hR false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralFramedPhysicalSquare.point IntegralMixedPhysicalFieldEquality.pointNewest

theorem center_field (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (i : ℕ)
    (hi : Nat.fromBitsLE (WordList.get (refs c) i) < IntegralMixedPhysicalFieldEquality.count hn ht ha hR c) :
    FormulaSignSlotRadialBankCenterTest.center B T H refs c w hv i =
      IntegralMixedPhysicalFieldEquality.point hn ht ha hR c w hv
        (Nat.fromBitsLE (WordList.get (refs c) i)) := by
  let j := Nat.fromBitsLE (WordList.get (refs c) i)
  have HR : FormulaSignSlotRadialBankCenterTest.raw B T H c w hv =
      IntegralFramedPhysicalBankTerm.rawScalar B T H c w hv := rfl
  have HE := IntegralFramedPhysicalBankTerm.env_coordinate B T H c w hv j hi
  unfold FormulaSignSlotRadialBankCenterTest.center
  rw [HR]
  apply HE.trans
  unfold IntegralMixedPhysicalFieldEquality.point IntegralMixedPhysicalFieldEquality.pointNewest
  apply congrArg (IntegralFramedPhysicalSquare.point _ _ _ _ _ _ _ _ _ c w hv)
  apply Fin.ext
  simp only [IntegralFramedPhysicalIntegerLeaves.coordinate, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    IntegralMixedPhysicalFieldEquality.newest]
  change IntegralMixedPhysicalFieldEquality.count hn ht ha hR c - 1 - j =
    min (IntegralMixedPhysicalFieldEquality.count hn ht ha hR c - 1 -
      min j (IntegralMixedPhysicalFieldEquality.count hn ht ha hR c - 1))
      (IntegralMixedPhysicalFieldEquality.count hn ht ha hR c - 1)
  omega

end LeanCanny.Encoding.FormulaSignSlotRadialMarkedCenterField
