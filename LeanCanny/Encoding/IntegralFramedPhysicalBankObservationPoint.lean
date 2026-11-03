/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalBankObservation
public import LeanCanny.Encoding.IntegralFramedPhysicalBankTermPoint
/-! # Retained observation quotients are the same chronological bank environment -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSuffixTest
open LeanCanny.Algebra LeanCanny.Computation
open IntegralFramedBankQuery (Bank)
open IntegralFramedPhysicalBankTerm (input)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem observation_eq_env (B : Bank) (T : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (input B) c w)
    (j : ℕ) (hj : j<(family B.parameters B.plan B.data).birth (B.key c)) :
    (IntegralMixedFramedBankObservation.ofState ((family B.parameters B.plan B.data).state (B.key c))).point
      (rawTuple B c w hv) ((family B.parameters B.plan B.data).birth (B.key c)-j-1)=
    IntegralFramedPhysicalBankTerm.env B T hr c w hv j :=by
  let i : Fin ((IntegralFramedBankQuery.input B).count c):=
    ⟨(family B.parameters B.plan B.data).birth (B.key c)-j-1,by
      change (family B.parameters B.plan B.data).birth (B.key c)-j-1<
        (family B.parameters B.plan B.data).birth (B.key c)
      omega⟩
  have HE:=IntegralFramedPhysicalBankTerm.env_coordinate B T hr c w hv j hj
  have HI : IntegralFramedPhysicalIntegerLeaves.coordinate B.parameters B.plan B.data B.key B.positive c
      (BinaryNatCode.encode j)=i :=by
    apply Fin.ext
    simp only [IntegralFramedPhysicalIntegerLeaves.coordinate,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    dsimp only [i]
    omega
  rw [HI] at HE
  exact (bank_point_observation B c w hv i).trans HE.symm

end LeanCanny.Encoding.IntegralFramedPhysicalSuffixTest
