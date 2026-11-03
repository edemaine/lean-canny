/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalSuffixPoint
public import LeanCanny.Encoding.SquareSampleCompleteCoordinateSign

/-! # Full raw scalar signs and actual retained-bank observations -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSuffixTest
open LeanCanny.Algebra LeanCanny.Computation
open IntegralFramedBankQuery (Bank)
open IntegralFramedPhysicalBankTerm (input)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (B : Bank) (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (input B) c w)

theorem bank_point_observation (i : Fin ((IntegralFramedBankQuery.input B).count c)) :
    (IntegralMixedFramedBankObservation.ofState ((family B.parameters B.plan B.data).state (B.key c))).point
      (rawTuple B c w hv) i.val=
    IntegralFramedPhysicalSquare.point B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive c w hv i :=by
  unfold rawTuple
  exact IntegralMixedFramedBankObservation.point_ofState _ _ i

variable (T : IntegralMixedHeaderTablesBits.Tables)
  (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)

theorem scalar_column_value (i : Fin ((IntegralFramedBankQuery.input B).count c)) :
    rawTuple B c w hv i.val=(SquareSampleCompleteVertices.candidate (input B) c w hv).val
      (IntegralMixedFramedPhysicalIndex.nativeScalarColumn B.parameters B.plan B.data T hr (B.key c)
        (Fin.cast (scalar_count B c) i)) :=by
  have HE : rawTuple B c w hv i.val=
      IntegralFramedPhysicalSquare.scalarTuple B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive c w hv i :=by
    unfold rawTuple
    exact dite_eq_left i.isLt
  rw [HE,IntegralFramedPhysicalSquare.scalarTuple_map]
  unfold IntegralMixedFramedScalarEmbedding.scalarMap
  rw [IntegralMixedFramedPhysicalIndex.nativeScalarColumn_eq]
  rfl

include hr in
theorem scalar_column_sign (i : Fin ((IntegralFramedBankQuery.input B).count c)) :
    SquareSampleCompleteCoordinateSign.value (input B)
      (pair (pair c w) (BinaryNatCode.encode (IntegralMixedFramedPhysicalIndex.scalarColumn B.parameters T
        (pair (B.key c) (BinaryNatCode.encode i.val)))))=
      InfinitesimalSign.encode (SignType.sign (rawTuple B c w hv i.val)) :=by
  have HP:=SquareSampleCompleteCoordinateSign.packet (input B) c w hv
    (IntegralMixedFramedPhysicalIndex.nativeScalarColumn B.parameters B.plan B.data T hr (B.key c)
      (Fin.cast (scalar_count B c) i))
  have HE:=HP.trans (congrArg (fun a : ℝ=>InfinitesimalSign.encode (SignType.sign a))
    (scalar_column_value B c w hv T hr i).symm)
  simpa only [IntegralMixedFramedPhysicalIndex.nativeScalarColumn,Fin.val_cast] using HE

end LeanCanny.Encoding.IntegralFramedPhysicalSuffixTest
