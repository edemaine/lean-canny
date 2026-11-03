/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalRowMass
public import LeanCanny.Algebra.PhysicalCriticalMassBudget
public import LeanCanny.Algebra.IntegralMixedGlobalHeightBounds
/-! # Full physical row mass from original numeric height profiles -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalRowBudget
open LeanCanny.Encoding LeanCanny.Computation MvPolynomial FlatAffineCriticalStage
open IntegralMixedHistory IntegralHistorySampler FixedWidthPolynomial IntegralCoordinateBasis
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def sourceC (F H : ℕ) := F*H+1
def bankG (F H : ℕ) := (F+3)*H+1
def normalExponent (S F H : ℕ) := (S+1)*bankG F H+2
def heightExponent (S B L F H : ℕ) := S*B+IntegralMixedGlobalHeightBounds.expressionFactor S L*bankG F H
def criticalExponent (n S B W D L F H : ℕ) := PhysicalCriticalMassBudget.exponent (n+1)
  (PhysicalCriticalMassBudget.sourceExponent (n+1) W (sourceC F H)) D
  (normalExponent S F H) (heightExponent S B L F H)
def exponent (n S B W D L F H : ℕ) := max (criticalExponent n S B W D L F H)
  (PaddedIntegralParameterExtension.rowMassHeight S B H)

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem new_physical_row (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n)
    (W D L F H : ℕ) (hH : 1≤H) (HG : x.bank.Bounds H)
    (hc : ∀e,(P.low.coeff e).natAbs≤2^sourceC F H)
    (ha : P.leading.natAbs.size≤sourceC F H) (hw : P.degree.size≤W) (hd : P.degree≤D)
    (hl : ∀i,(r.heights i).nodes≤L)
    (he : ∀i,(r.heights i).CoefficientsBound (sourceC F H))
    (hs : ∀i,(r.scales i).natAbs.size≤sourceC F H)
    (j : Variables (n+1)) :
    MvMass.mass ((IntegralHistorySampler.criticalStep x.sampler (data x hm r)).rows (Sum.inr j))≤
      2^criticalExponent n S B W D L F H := by
  have hG : H≤bankG F H := by unfold bankG; nlinarith
  have hC : sourceC F H+1≤bankG F H := by unfold sourceC bankG; nlinarith
  have HB : x.bank.Bounds (bankG F H) := HG.mono hG
  have HE : retainedBudget m (bankG F H) r≤IntegralMixedGlobalHeightBounds.expressionFactor S L*bankG F H :=
    IntegralMixedGlobalHeightBounds.retainedBudget_scaled r m S L (sourceC F H) (bankG F H) hm hl he hC
  have HR : ∀i,MvMass.mass (historyHeights x.sampler (data x hm r).heights i)≤2^heightExponent S B L F H := by
    intro i
    apply (historyHeights_mass x.sampler (data x hm r).heights (retainedBudget m (bankG F H) r)
      (data_height_matrix_bound x hm r _ HB) i).trans
    have HX : count m B*2^retainedBudget m (bankG F H) r=2^(B*m+retainedBudget m (bankG F H) r) := by
      unfold count
      rw [←pow_mul,←pow_add]
    rw [HX]
    exact Nat.pow_le_pow_right (by decide) (by unfold heightExponent; nlinarith)
  have HN : ∀k i,(PhysicalPowerCriticalRows.coordinateNormals (data x hm r).objective (data x hm r).scales
      (data x hm r).free k i).natAbs≤2^normalExponent S F H := by
    intro k i
    apply (data_normal_bound x hm r (bankG F H) (sourceC F H) HB
      (fun i=>(Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) (hs i))) k i).trans
    have HT : m*bankG F H+sourceC F H≤(S+1)*bankG F H := by nlinarith
    have HP : 1≤2^((S+1)*bankG F H) := Nat.one_le_two_pow
    have HM := Nat.pow_le_pow_right (n:=2) (by decide) HT
    unfold physicalNormalBound normalExponent
    conv_rhs => rw [pow_add]
    norm_num only [pow_two]
    nlinarith
  have HM : MvMass.mass (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)≤
      2^PhysicalCriticalMassBudget.sourceExponent (n+1) W (sourceC F H) :=
    PhysicalCriticalMassBudget.source_mass P.low P.leading P.degree W (sourceC F H) P.low_degree hw hc
      ((Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) ha))
  apply (CoordinatePowerSubstitution.mass_le _ _).trans
  apply (FlatAffineCriticalStage.mass_le _ (data x hm r).frozen _ _ (2^normalExponent S F H)
    (2^heightExponent S B L F H) HN HR j).trans
  exact PhysicalCriticalMassBudget.flat_bound _ _ D _ _ HM
    ((FermatCriticalHomogenization.polynomial_degree P.low P.leading P.degree P.low_degree).trans hd)

end LeanCanny.Algebra.IntegralMixedPhysicalRowBudget
