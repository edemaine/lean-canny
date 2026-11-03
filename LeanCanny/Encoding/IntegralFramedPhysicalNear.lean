/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalTarskiSelected
public import LeanCanny.Encoding.OrderedWindowStatisticFP
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateNearQueries
/-! # A total native endpoint test with same-full-vertex Near semantics

The test computes five integer statistics. Its semantic contract constructs
one old interpreting hom from the full vertex; it never receives a hom or
an independent old root label. Physical branch anchoring remains separate.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalNear
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralFramedTerminalTarskiStatistic.value RealIteratedTarski.value

def reset (u : List Bool) :=pair (pairFst u) []
theorem reset_FP : reset∈FP:=mem_FP_pair pairFst_mem_FP (constFn_mem_FP [])

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (center selected : List Bool→ℕ)
variable (hpos : ∀q,0<(family P D H).birth (terminal q))
variable (hfactor : ∀root,1≤F root) (hf : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
variable (right : Bool)

noncomputable def packet (u : List Bool) :=OrderedWindowStatisticBits.pack (pairSnd u)
  (SignStatisticBits.integerCode (IntegralFramedTerminalTarskiStatistic.value P D H L F C hs parent terminal center selected hpos hfactor hf
    0 right false (reset u)))
  (SignStatisticBits.integerCode (IntegralFramedTerminalTarskiStatistic.value P D H L F C hs parent terminal center selected hpos hfactor hf
    2 right false (reset u)))
  (SignStatisticBits.integerCode (IntegralFramedTerminalTarskiStatistic.value P D H L F C hs parent terminal center selected hpos hfactor hf
    1 right false (reset u)))
  (SignStatisticBits.integerCode (IntegralFramedTerminalTarskiStatistic.value P D H L F C hs parent terminal center selected hpos hfactor hf
    2 right true (reset u)))
  (SignStatisticBits.integerCode (IntegralFramedTerminalTarskiStatistic.value P D H L F C hs parent terminal center selected hpos hfactor hf
    1 right true (reset u)))

noncomputable def Accept : Language :=
  {u | OrderedWindowStatisticBits.Accept (packet P D H L F C hs parent terminal center selected hpos hfactor hf right u)}

variable (q w : List Bool)
local notation "G" => family P D H
local notation "oldKey" => IntegralMixedVirtualTaskBits.saved P (parent q)
local notation "x" => IntegralMixedCutSource.Family.state (family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "r" => IntegralMixedCutSource.Family.rule (family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "j" => IntegralMixedCoordinateCoefficientSnapshot.coordinate (family P D H)
  (IntegralMixedVirtualTaskBits.saved P (parent q)) (get P Field.slot13 (parent q))

theorem exists_near_iff
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w)
    (hcore : IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q)
    (hcount : IntegralMixedFramedTerminalCoordinateHeadBits.Valid P D H parent terminal q)
    (hroot : pairFst (terminal q)=pairFst oldKey)
    (hi : center q<(IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count)
    (hj : selected q<(IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count)
    {a b : ℝ} (hab : a<b)
    (hanchor : IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P D H (terminal q))
      (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨center q,hi⟩=
        if right then b else a) (code : ℕ) :
    ∃φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P (parent q))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
        IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv
          (UniformIntegralPowerSchedule.embed hcount i)^
          UniformIntegralPowerSchedule.weights ((G).cap oldKey) (2^(G).width oldKey) ((G).birth oldKey) i) ∧
      (pair (pair q w) (BinaryNatCode.encode code)∈Accept P D H L F C hs parent terminal center selected hpos hfactor hf right↔
        LeanCanny.Connectivity.IntegralMixedSelectedCoordinateEndpoint.Near x ((G).birth_bound oldKey) r φ a b
          (if right then b else a) j code
          (IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P D H (terminal q))
            (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨selected q,hj⟩)) :=by
  obtain ⟨φ,hφ,HV⟩:=IntegralFramedPhysicalTarskiSelected.exists_selected_values P D H L F C hs parent terminal center selected hpos
    hfactor hf q w hv hcore hcount hroot hi hj
  refine ⟨φ,hφ,?_⟩
  have HT : pair (pair q w) (BinaryNatCode.encode code)∈Accept P D H L F C hs parent terminal center selected hpos hfactor hf right↔
      LeanCanny.Connectivity.IntegralMixedSelectedCoordinateNearQueries.test x ((G).birth_bound oldKey) r φ j
        (IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P D H (terminal q))
          (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨center q,hi⟩)
        right (IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).common
        (IntegralMixedFramedTerminalTarskiSelected.allowance P D H L F C hs parent terminal center q)
        (IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P D H (terminal q))
          (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨selected q,hj⟩)
        (((IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).common:ℝ)^2) code :=by
    unfold Accept packet reset
    simp only [Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair]
    rw [OrderedWindowStatisticBits.packet,HV 0 right false,HV 2 right false,HV 1 right false,HV 2 right true,HV 1 right true]
    rfl
  rw [hanchor] at HT
  apply HT.trans
  exact (LeanCanny.Connectivity.IntegralMixedSelectedCoordinateNearQueries.near_iff x ((G).birth_bound oldKey) r φ j
    (IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).common
    (IntegralMixedFramedBankTermSign.common_ne_zero P D H (terminal q))
    (IntegralMixedFramedTerminalTarskiSelected.allowance P D H L F C hs parent terminal center q)
    (IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P D H (terminal q))
      (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨selected q,hj⟩)
    (((IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).common:ℝ)^2)
    (sq_pos_of_ne_zero (Int.cast_ne_zero.mpr (IntegralMixedFramedBankTermSign.common_ne_zero P D H (terminal q))))
    hab right code).symm

end LeanCanny.Encoding.IntegralFramedPhysicalNear
