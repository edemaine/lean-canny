/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedZeroTarskiStatisticValue
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateRank
public import LeanCanny.Encoding.OrderedWindowStatisticFP
/-! # Zero-parameter statistics identify an actual selected root ordinal -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedZeroTarskiStatistic
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family value

private theorem packet_word (word : List Bool) (v0 vl2 vl1 vh2 vh1 : ℤ) :
    OrderedWindowStatisticBits.Accept (OrderedWindowStatisticBits.pack word
      (SignStatisticBits.integerCode v0) (SignStatisticBits.integerCode vl2) (SignStatisticBits.integerCode vl1)
      (SignStatisticBits.integerCode vh2) (SignStatisticBits.integerCode vh1))↔
    2*v0≤2*(Nat.fromBitsLE word:ℤ)+vl2+vl1 ∧2*(Nat.fromBitsLE word:ℤ)<vh2-vh1 :=by
  simp only [OrderedWindowStatisticBits.Accept,OrderedWindowStatisticBits.positive,
    OrderedWindowStatisticBits.negative,OrderedWindowStatisticBits.pack,OrderedWindowStatisticBits.unit,
    OrderedWindowStatisticBits.lowerSquare,OrderedWindowStatisticBits.lower,OrderedWindowStatisticBits.upperSquare,
    OrderedWindowStatisticBits.upper,SignStatisticBits.integerCode,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]
  omega

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (parent terminal : List Bool→List Bool) (selected : List Bool→ℕ)
  (hpos : ∀q,0<(family P D H).birth (terminal q))
  (hf : ∀root,1≤F root) (hdefault : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)

noncomputable def rankPacket (q w code : List Bool):=OrderedWindowStatisticBits.pack code
  (SignStatisticBits.integerCode (value P D H L F C hs parent terminal selected hpos hf hdefault 0 false (pair (pair q w) [])))
  (SignStatisticBits.integerCode (value P D H L F C hs parent terminal selected hpos hf hdefault 2 false (pair (pair q w) [])))
  (SignStatisticBits.integerCode (value P D H L F C hs parent terminal selected hpos hf hdefault 1 false (pair (pair q w) [])))
  (SignStatisticBits.integerCode (value P D H L F C hs parent terminal selected hpos hf hdefault 2 true (pair (pair q w) [])))
  (SignStatisticBits.integerCode (value P D H L F C hs parent terminal selected hpos hf hdefault 1 true (pair (pair q w) [])))

variable (q w code : List Bool)
local notation "G"=>family P D H
local notation "oldKey"=>IntegralMixedVirtualTaskBits.saved P (parent q)
local notation "x"=>IntegralMixedCutSource.Family.state G oldKey
local notation "r"=>IntegralMixedCutSource.Family.rule G oldKey
local notation "j"=>IntegralMixedCoordinateCoefficientSnapshot.coordinate G oldKey (get P Field.slot13 (parent q))
local notation "d"=>IntegralMixedSelectedCoordinateHead.fullDegree P G parent q

noncomputable def RankAt
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w)
    (hcount : IntegralMixedFramedTerminalCoordinateHeadBits.Valid P D H parent terminal q)
    (hi : selected q<(IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count) : Prop:=
  ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv
        (UniformIntegralPowerSchedule.embed hcount i)^
        UniformIntegralPowerSchedule.weights ((G).cap oldKey) (2^(G).width oldKey) ((G).birth oldKey) i) ∧
    let p:=(IntegralMixedCriticalSweep.selected x ((G).birth_bound oldKey) r j φ).map (Polynomial.evalRingHom 0)
    let y:=IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P D H (terminal q))
      (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨selected q,hi⟩
    y∈p.roots.toFinset ∧OrderedRealRootWindow.rank p.roots.toFinset y=Nat.fromBitsLE code

theorem rankPacket_iff
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w)
    (hc : IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q)
    (hcount : IntegralMixedFramedTerminalCoordinateHeadBits.Valid P D H parent terminal q)
    (hi : selected q<(IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count)
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv
        (UniformIntegralPowerSchedule.embed hcount i)^
        UniformIntegralPowerSchedule.weights ((G).cap oldKey) (2^(G).width oldKey) ((G).birth oldKey) i) :
    OrderedWindowStatisticBits.Accept (rankPacket P D H L F C hs parent terminal selected hpos hf hdefault q w code)↔
      let p:=(IntegralMixedCriticalSweep.selected x ((G).birth_bound oldKey) r j φ).map (Polynomial.evalRingHom 0)
      let y:=LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
        (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q))
        (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨selected q,hi⟩
      y∈p.roots.toFinset ∧LeanCanny.Geometry.OrderedRealRootWindow.rank p.roots.toFinset y=Nat.fromBitsLE code :=by
  have HV (e : Fin 3) (negative : Bool):=value_selected P D H L F C hs parent terminal selected hpos q hf hdefault
    e negative w hv hc hcount hi φ hφ
  unfold rankPacket
  rw [packet_word,HV 0 false,HV 2 false,HV 1 false,HV 2 true,HV 1 true]
  have HD : 0<d:=by
    rw [IntegralMixedFramedCoordinatePackedSelected.fullDegree_eq]
    unfold PurePowerReductionBounds.dimension FixedWidthPolynomial.count
    exact pow_pos (pow_pos (by decide) _) _
  have HP : ((IntegralMixedCriticalSweep.selected x ((G).birth_bound oldKey) r j φ).map
      (Polynomial.evalRingHom 0)).natDegree=d:=by
    rw [IntegralMixedFramedCoordinatePackedSelected.fullDegree_eq]
    exact IntegralMixedCriticalSweep.specialized_degree x ((G).birth_bound oldKey) r j φ 0
  exact LeanCanny.Connectivity.IntegralMixedSelectedCoordinateRank.test_iff_rank _ d HD HP _ _
    (sq_pos_of_ne_zero (Int.cast_ne_zero.mpr (IntegralMixedFramedBankTermSign.common_ne_zero P D H (terminal q)))) _


theorem exists_rankPacket_iff
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w)
    (hc : IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q)
    (hcount : IntegralMixedFramedTerminalCoordinateHeadBits.Valid P D H parent terminal q)
    (hroot : pairFst (terminal q)=pairFst oldKey)
    (hi : selected q<(IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
        IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv
          (UniformIntegralPowerSchedule.embed hcount i)^
          UniformIntegralPowerSchedule.weights ((G).cap oldKey) (2^(G).width oldKey) ((G).birth oldKey) i) ∧
      (OrderedWindowStatisticBits.Accept (rankPacket P D H L F C hs parent terminal selected hpos hf hdefault q w code)↔
        let p:=(IntegralMixedCriticalSweep.selected x ((G).birth_bound oldKey) r j φ).map (Polynomial.evalRingHom 0)
        let y:=LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q))
          (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨selected q,hi⟩
        y∈p.roots.toFinset ∧LeanCanny.Geometry.OrderedRealRootWindow.rank p.roots.toFinset y=Nat.fromBitsLE code) :=by
  obtain ⟨φ,hφ⟩:=IntegralFramedPhysicalOlderParent.exists_interpretation P D H L F C hs terminal hpos q w hv oldKey hroot hcount
  exact ⟨φ,hφ,rankPacket_iff P D H L F C hs parent terminal selected hpos hf hdefault q w code hv hc hcount hi φ hφ⟩


theorem rankPacket_rankAt_iff
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w)
    (hc : IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q)
    (hcount : IntegralMixedFramedTerminalCoordinateHeadBits.Valid P D H parent terminal q)
    (hroot : pairFst (terminal q)=pairFst oldKey)
    (hi : selected q<(IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count) :
    OrderedWindowStatisticBits.Accept (rankPacket P D H L F C hs parent terminal selected hpos hf hdefault q w code)↔
      RankAt P D H L F C hs parent terminal selected hpos q w code hv hcount hi :=by
  constructor
  · intro HA
    obtain ⟨φ,hφ,HK⟩:=exists_rankPacket_iff P D H L F C hs parent terminal selected hpos hf hdefault q w code
      hv hc hcount hroot hi
    exact ⟨φ,hφ,HK.mp HA⟩
  · rintro ⟨φ,hφ,HK⟩
    exact (rankPacket_iff P D H L F C hs parent terminal selected hpos hf hdefault q w code hv hc hcount hi φ hφ).mpr HK

end LeanCanny.Encoding.IntegralFramedZeroTarskiStatistic
