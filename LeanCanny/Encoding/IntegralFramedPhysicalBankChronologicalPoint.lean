/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalBankTermPoint
/-! # A bank environment reads its chronological scalar from the full word -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalBankTerm
open LeanCanny.Algebra LeanCanny.Computation
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedHistoryFamilyBits (family)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] env IntegralFramedPhysicalSquare.point

theorem env_chronological (B : Bank) (T : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (input B) c w)
    (i : ℕ) (hi : i<(IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data (B.key c)).count) :
    env B T hr c w hv i=IntegralFramedPhysicalSquare.point B.parameters B.plan B.data B.nodes B.factor B.seed
      B.bounds B.key B.positive c w hv
      ⟨(family B.parameters B.plan B.data).birth (B.key c)-1-i,by
        have H : 0<(family B.parameters B.plan B.data).birth (B.key c):=B.positive c
        omega⟩ :=by
  rw [env_coordinate B T hr c w hv i hi]
  apply congrArg (IntegralFramedPhysicalSquare.point B.parameters B.plan B.data B.nodes B.factor B.seed
    B.bounds B.key B.positive c w hv)
  apply Fin.ext
  simp only [IntegralFramedPhysicalIntegerLeaves.coordinate,BinaryNatCode.encode,Nat.fromBitsLE_bits]

end LeanCanny.Encoding.IntegralFramedPhysicalBankTerm
