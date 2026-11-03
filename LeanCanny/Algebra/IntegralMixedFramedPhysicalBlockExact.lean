/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockData
public import LeanCanny.Algebra.PhysicalCoordinateRowBranches
/-! # Native branch polynomials are literal unpowered critical rows -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask MvPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedPhysicalSourceAtBits (family)
open IntegralMixedFramedPhysicalHeightBits (Active)
open FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] MvPolynomial.pderiv MvPolynomial.rename

noncomputable def unpoweredExact (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (j : Variables (spatialCount P D J base q)) :=
  let F:=family P D J base
  let d:=criticalData P D J base q
  rename (columns P D J base q) (FlatAffineCriticalStage.row
    (IntegralMixedPhysicalOriginalSourceBits.polynomial F q) d.frozen
    (PhysicalPowerCriticalRows.coordinateNormals 2 d.scales d.free)
    (IntegralHistorySampler.historyHeights (F.state q).sampler d.heights) j)

theorem sourcePolynomial_exact (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) :
    sourcePolynomial P D J base q=unpoweredExact P D J base q (.inr 0) := by
  rw [unpoweredExact,PhysicalPowerCriticalRows.renamed_equation]
  have HE : columns P D J base q∘ambient=ambientIndex P D J base q := by
    funext i
    exact columns_ambient P D J base q i
  rw [HE]
  rfl

theorem rawGradient_exact (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (selected : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) (hq : Active P (base q)) :
    rawGradient P D J base selected hs q=
      unpoweredExact P D J base q (.inl ⟨selected q,hs q⟩) := by
  rw [unpoweredExact,PhysicalPowerCriticalRows.renamed_gradient]
  have HE : columns P D J base q∘ambient=ambientIndex P D J base q := by
    funext i
    exact columns_ambient P D J base q i
  have HF : ((⟨selected q,hs q⟩ : Fin (spatialCount P D J base q))=(criticalData P D J base q).free)↔
      selected q=freeIndex P D J base q := by
    rw [Fin.ext_iff]
    rfl
  rw [HE]
  simp only [HF,columns_multiplier]
  rw [rawGradient,normalPolynomial_eq P D J base selected hs q hq]
  rfl

theorem heightRow_exact (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (base : List Bool→List Bool) (selected : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) (hq : Active P (base q))
    (hi : get P .slot8 (base q)=selected q) :
    heightRowPolynomial P D J T hr base selected hs q=
      unpoweredExact P D J base q (.inr (⟨selected q,hs q⟩ : Fin (spatialCount P D J base q)).succ) := by
  rw [unpoweredExact,PhysicalPowerCriticalRows.renamed_height]
  have HF : ((⟨selected q,hs q⟩ : Fin (spatialCount P D J base q))∈(criticalData P D J base q).frozen)↔
      selected q<((family P D J base).rule q).offset.val := by
    simp only [criticalData,IntegralMixedHistory.data,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [HF,columns_ambient,columns_multiplier]
  rw [heightRowPolynomial,ite_eq_left hq]
  by_cases h : selected q<((family P D J base).rule q).offset.val
  · rw [ite_eq_left h,ite_eq_left h,activeHeightPolynomial,
      normalAmbientPolynomial_eq P D J base selected hs q hq,heightPolynomial_eq P D J T hr base selected hs q hq hi]
  · rw [ite_eq_right h,ite_eq_right h]
    rfl

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
