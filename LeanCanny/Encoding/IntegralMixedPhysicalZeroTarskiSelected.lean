/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalZeroTarskiNative
public import LeanCanny.Encoding.IntegralFramedZeroTarskiStatisticValue
public import LeanCanny.Connectivity.IntegralMixedSelectedAnchorWindow
/-! # The five original-only statistics recognize the selected head at zero

A valid full word supplies one older interpreting hom for all five tests.
The root and count hypotheses refer to this word's actual terminal sampler;
no word, root, or context is replaced. Acceptance has an ordinal meaning only
on the stated active-source and selected-coordinate domain.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalZeroTarski
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank)
open IntegralMixedPhysicalTraceCutTest (factor_positive fallback)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] bank IntegralMixedFramedHistoryFamilyBits.family RealIteratedTarski.value
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
  (parent : List Bool→List Bool) (selected : List Bool→ℕ) (q w : List Bool)
local notation "B" => bank hn ht ha hR outer
local notation "P" => IntegralFramedBankQuery.Bank.parameters (bank hn ht ha hR outer)
local notation "D" => IntegralFramedBankQuery.Bank.plan (bank hn ht ha hR outer)
local notation "H" => IntegralFramedBankQuery.Bank.data (bank hn ht ha hR outer)
local notation "G" => IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "oldKey" => IntegralMixedVirtualTaskBits.saved P (parent q)
local notation "x" => IntegralMixedCutSource.Family.state (IntegralMixedFramedHistoryFamilyBits.family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "r" => IntegralMixedCutSource.Family.rule (IntegralMixedFramedHistoryFamilyBits.family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "j" => IntegralMixedCoordinateCoefficientSnapshot.coordinate (IntegralMixedFramedHistoryFamilyBits.family P D H)
  (IntegralMixedVirtualTaskBits.saved P (parent q)) (get P Field.slot13 (parent q))
local notation "fd" => IntegralMixedSelectedCoordinateHead.fullDegree P (IntegralMixedFramedHistoryFamilyBits.family P D H) parent q

theorem exists_language_iff
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) q w)
    (hcore : IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q)
    (hcount : IntegralMixedFramedTerminalCoordinateHeadBits.Valid P D H parent (B).key q)
    (hroot : pairFst ((B).key q)=pairFst oldKey)
    (hi : selected q<(IntegralMixedFramedBankSnapshotBits.atKey P D H ((B).key q)).count)
    (code : List Bool→ℕ) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      let p:=(IntegralMixedCriticalSweep.selected x ((G).birth_bound oldKey) r j φ).map (Polynomial.evalRingHom 0)
      let y:=LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
        (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H ((B).key q))
        (IntegralFramedPhysicalSquare.scalarTuple P D H (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive q w hv)
        ⟨selected q,hi⟩
      pair q w∈language hn ht ha hR outer parent selected code↔
        y∈p.roots.toFinset ∧ OrderedRealRootWindow.rank p.roots.toFinset y=code q :=by
  obtain ⟨φ,HV⟩:=IntegralFramedZeroTarskiStatistic.exists_selected P D H (B).nodes (B).factor (B).seed (B).bounds
    parent (B).key selected (B).positive q (factor_positive hn ht ha hR outer) (fallback hn ht ha hR outer)
    w hv hcore hcount hroot hi
  let p:=(IntegralMixedCriticalSweep.selected x ((G).birth_bound oldKey) r j φ).map (Polynomial.evalRingHom 0)
  let y:=LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
    (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H ((B).key q))
    (IntegralFramedPhysicalSquare.scalarTuple P D H (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive q w hv)
    ⟨selected q,hi⟩
  let scale:ℝ:=((IntegralMixedFramedBankSnapshotBits.atKey P D H ((B).key q)).common:ℝ)^2
  have HV' (power : Fin 3) (negative : Bool) :
      value hn ht ha hR outer parent selected power negative (pair q w)=
        LeanCanny.Connectivity.IntegralMixedSelectedAnchorWindow.value p fd y scale negative power :=HV power negative
  have HP :p.natDegree=fd :=
    (IntegralMixedCriticalSweep.specialized_degree x ((G).birth_bound oldKey) r j φ 0).trans
      (IntegralMixedFramedCoordinatePackedSelected.fullDegree_eq P D H parent q).symm
  have HD :0<fd :=by
    rw [IntegralMixedFramedCoordinatePackedSelected.fullDegree_eq]
    unfold PurePowerReductionBounds.dimension FixedWidthPolynomial.count
    exact pow_pos (pow_pos (by decide) _) _
  have HS :0<scale :=by
    apply sq_pos_of_ne_zero
    exact_mod_cast LeanCanny.Geometry.IntegralMixedFramedBankTermSign.common_ne_zero P D H ((B).key q)
  refine ⟨φ,?_⟩
  change pair q w∈language hn ht ha hR outer parent selected code↔
    y∈p.roots.toFinset ∧ OrderedRealRootWindow.rank p.roots.toFinset y=code q
  rw [←LeanCanny.Connectivity.IntegralMixedSelectedAnchorWindow.test_iff p fd HD HP y scale HS (code q)]
  rw [packet_iff]
  simp only [pairFst_pair,HV']
  rfl
end LeanCanny.Encoding.IntegralMixedPhysicalZeroTarski
