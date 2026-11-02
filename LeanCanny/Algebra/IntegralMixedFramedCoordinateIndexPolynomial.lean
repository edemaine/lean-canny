/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateIndex
/-! # Full symbolic coordinate coefficients from one unchanged old key -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateIndexBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCoordinateRepresentativeBits (atContext)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

theorem scalar_cap (P : Parameters) (q : List Bool) :
    2^P.width (RankedHistoryTask.root q)≤numericCap P (RankedHistoryTask.root q) :=
  (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.2.2.2.1

theorem coordinate_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (y : ℕ) (hy : y<IntegralMixedCoordinateCoefficientTasks.choiceBound P (family P D H) q) :
    y≤2^P.width (RankedHistoryTask.root q) := by
  let key:=IntegralMixedVirtualTaskBits.saved P q
  have HC:=IntegralMixedExceptionalBounds.coordinateCap_le ((family P D H).spatial key).degree ((family P D H).rule key)
  have HA : IntegralMixedExceptionalBounds.K ((family P D H).ambient key+1) ((family P D H).spatial key).degree≤
      IntegralMixedExceptionalBounds.auxiliaryCap ((family P D H).ambient key+1) ((family P D H).spatial key).degree := by
    unfold IntegralMixedExceptionalBounds.auxiliaryCap
    omega
  have HX:=HC.trans (HA.trans ((family P D H).scalar_cap key))
  rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width q] at HX
  have HY : y≤PurePowerReductionBounds.dimension ((family P D H).ambient key-((family P D H).rule key).critical.offset.val+1)
      ((family P D H).spatial key).degree := by
    change y<PurePowerReductionBounds.dimension
      ((family P D H).ambient key-((family P D H).rule key).critical.offset.val+1)
      ((family P D H).spatial key).degree+1 at hy
    omega
  exact HY.trans HX

theorem polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (y k : List Bool→ℕ) (q : List Bool)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P (parent q))
    (hj : get P .slot13 (parent q)≤P.ambient (RankedHistoryTask.root (parent q))+1)
    (hy : y q<IntegralMixedCoordinateCoefficientTasks.choiceBound P (family P D H) (parent q))
    (hk : k q<2^P.width (RankedHistoryTask.root (parent q))) :
    HEq (IntegralMixedFramedAllCoordinateSourceBits.polynomial P D H (query P parent y k q))
      (atContext P D H (IntegralMixedFramedAllCoordinateSourceBits.horizon P (parent q))
        (IntegralMixedVirtualTaskBits.saved P (parent q)) (get P .slot13 (parent q)) (y q) (k q)) := by
  have HY:=(coordinate_bound P D H (parent q) (y q) hy).trans (scalar_cap P (parent q))
  have HK:=hk.le.trans (scalar_cap P (parent q))
  have HA:=active P D H parent y k q ha hj hy (coordinate_bound P D H (parent q) (y q) hy) HY
  have HS:=IntegralMixedFramedCoordinateRepresentativeBits.source P D H (query P parent y k q) HA
  have HC:=IntegralMixedFramedCoordinateRepresentativeBits.atContext_congr P D H
    (IntegralMixedFramedAllCoordinateSourceBits.horizon P (query P parent y k q))
    (IntegralMixedFramedAllCoordinateSourceBits.horizon P (parent q)) _ _ _ _ _ _ _ _
    (by unfold IntegralMixedFramedAllCoordinateSourceBits.horizon; rw [root]) (saved P parent y k q)
    (other P parent y k q .slot13 (by decide) (by decide) (by decide))
    (y_value P parent y k q HY) (k_value P parent y k q HK)
  exact HS.trans HC

theorem atContext_outside (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (S : ℕ) (key : List Bool) (j y k : ℕ)
    (hout : IntegralMixedCoordinateTrailing.ChoiceBound ((family P D H).spatial key) ((family P D H).rule key)≤y ∨
      2^(family P D H).width key≤k) : atContext P D H S key j y k=0 := by
  let := ((family P D H).state key).sampler.scalarPrefix.ring
  have HZ : ((IntegralMixedCriticalSweep.coordinate ((family P D H).state key) ((family P D H).birth_bound key)
      ((family P D H).rule key) (IntegralMixedCoordinateCoefficientSnapshot.coordinate (family P D H) key j)).coeff y).coeff k=0 := by
    by_cases hy : y<IntegralMixedCoordinateTrailing.ChoiceBound ((family P D H).spatial key) ((family P D H).rule key)
    · have HK : 2^(family P D H).width key≤k:=hout.resolve_left (Nat.not_le.mpr hy)
      have HD:=IntegralMixedCutNilpotent.factor_degree_lt ((family P D H).state key) ((family P D H).birth_bound key)
        ((family P D H).rule key) (IntegralMixedRelativeCuts.Kind.coordinate
          (IntegralMixedCoordinateCoefficientSnapshot.coordinate (family P D H) key j) ⟨y,hy⟩)
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (HD.trans_le (((family P D H).scalar_cap key).trans HK))
    · have HY : PurePowerReductionBounds.dimension ((family P D H).ambient key-((family P D H).rule key).critical.offset.val+1)
          ((family P D H).spatial key).degree<y := by
        change ¬y<_+1 at hy
        omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((IntegralMixedCriticalSweep.coordinate_degree
        ((family P D H).state key) ((family P D H).birth_bound key) ((family P D H).rule key)
        (IntegralMixedCoordinateCoefficientSnapshot.coordinate (family P D H) key j)).trans_lt HY),Polynomial.coeff_zero]
  unfold atContext SelectedPoweredPolynomialLift.representative
  rw [HZ,IntegralCoordinateBasis.representative_zero,map_zero]

end LeanCanny.Algebra.IntegralMixedFramedCoordinateIndexBits
