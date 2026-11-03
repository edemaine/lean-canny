/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalTarskiStatisticValue
public import LeanCanny.Encoding.IntegralFramedPhysicalOlderParent
/-! # A full vertex supplies one old hom for every native endpoint statistic

No old vertex, root lifting, hom evaluator or separate coefficient sign
oracle is a premise. All six window queries retain the same old hom.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalTarskiSelected
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  RealIteratedTarski.value IntegralFramedTerminalTarskiStatistic.value

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (center selected : List Bool→ℕ)
variable (hpos : ∀q,0<(family P D H).birth (terminal q))
variable (hfactor : ∀root,1≤F root) (hf : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
variable (q w : List Bool)
local notation "G" => family P D H
local notation "oldKey" => IntegralMixedVirtualTaskBits.saved P (parent q)
local notation "x" => IntegralMixedCutSource.Family.state (family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "r" => IntegralMixedCutSource.Family.rule (family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "j" => IntegralMixedCoordinateCoefficientSnapshot.coordinate (family P D H)
  (IntegralMixedVirtualTaskBits.saved P (parent q)) (get P Field.slot13 (parent q))

theorem exists_selected_values
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w)
    (hcore : IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q)
    (hcount : IntegralMixedFramedTerminalCoordinateHeadBits.Valid P D H parent terminal q)
    (hroot : pairFst (terminal q)=pairFst oldKey)
    (hi : center q<(IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count)
    (hj : selected q<(IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count) :
    ∃φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P (parent q))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
        IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv
          (UniformIntegralPowerSchedule.embed hcount i)^
          UniformIntegralPowerSchedule.weights ((G).cap oldKey) (2^(G).width oldKey) ((G).birth oldKey) i) ∧
      ∀power : Fin 3,∀negativeEta negativeEpsilon : Bool,
        IntegralFramedTerminalTarskiStatistic.value P D H L F C hs parent terminal center selected hpos hfactor hf
          power negativeEta negativeEpsilon (pair (pair q w) [])=
        IntegralMixedSelectedCoordinateOrderedQueries.value
          (IntegralMixedSelectedCoordinateAffineDegree.head x ((G).birth_bound oldKey) r j φ
            (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
              (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q))
              (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨center q,hi⟩)
            negativeEta (IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).common
              (IntegralMixedFramedTerminalTarskiSelected.allowance P D H L F C hs parent terminal center q))
          (PurePowerReductionBounds.dimension ((G).ambient oldKey-(r).critical.offset.val+1) ((G).spatial oldKey).degree)
          (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
            (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q))
            (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨selected q,hj⟩)
          (((IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).common:ℝ)^2) negativeEpsilon power :=by
  obtain ⟨φ,hφ⟩:=IntegralFramedPhysicalOlderParent.exists_interpretation P D H L F C hs terminal hpos q w hv oldKey hroot hcount
  refine ⟨φ,hφ,fun power negativeEta negativeEpsilon=>?_⟩
  rw [IntegralFramedTerminalTarskiStatistic.value_at P D H L F C hs parent terminal center selected hpos hfactor hf
    power negativeEta negativeEpsilon q w hv]
  exact IntegralMixedFramedTerminalTarskiSelected.model_selected P D H L F C hs parent terminal center selected q hcore hcount hi hj φ
    (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) hφ (fun _=>power) negativeEta negativeEpsilon

end LeanCanny.Encoding.IntegralFramedPhysicalTarskiSelected
