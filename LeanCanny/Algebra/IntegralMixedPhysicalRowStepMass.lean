/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalRowBudget
public import LeanCanny.Algebra.IntegralMixedFullScriptHeight
/-! # Every full mixed command preserves the derived physical-row mass ceiling -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalRowBudget
open LeanCanny.Encoding LeanCanny.Computation MvPolynomial FlatAffineCriticalStage
open IntegralMixedHistory IntegralHistorySampler FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem full_step (x : State P S B m ι) (hm : m≤S)
    (c : IntegralMixedFullHistoryScript.Command P B) (W D L F H : ℕ)
    (hH : 1≤H) (HG : x.bank.Bounds H)
    (hc : ∀e,(P.low.coeff e).natAbs≤2^sourceC F H)
    (ha : P.leading.natAbs.size≤sourceC F H) (hw : P.degree.size≤W) (hd : P.degree≤D)
    (hcmd : IntegralMixedFullScriptHeight.CommandBounds (sourceC F H) L c)
    (ho : ∀i,MvMass.mass (x.sampler.rows i)≤2^exponent n S B W D L F H)
    (HN : (IntegralMixedFullHistoryScript.step x hm c).bank.Bounds H)
    (j : IntegralMixedFullHistoryScript.NextIndex ι c) :
    MvMass.mass ((IntegralMixedFullHistoryScript.step x hm c).sampler.rows j)≤2^exponent n S B W D L F H := by
  have HR : 2^PaddedIntegralParameterExtension.rowMassHeight m B H≤2^exponent n S B W D L F H :=
    Nat.pow_le_pow_right (by decide) ((by unfold PaddedIntegralParameterExtension.rowMassHeight; nlinarith :
      PaddedIntegralParameterExtension.rowMassHeight m B H≤PaddedIntegralParameterExtension.rowMassHeight S B H).trans (Nat.le_max_right _ _))
  have HC : 2^criticalExponent n S B W D L F H≤2^exponent n S B W D L F H :=
    Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _)
  cases c with
  | integer p hp hb =>
    exact (scalarStep_row_mass x.sampler hm _ _ (2^exponent n S B W D L F H) H ho
      (fun u v=>HN.numerator 0 u v) j).trans (max_le le_rfl HR)
  | critical r =>
    have HI : ∀v,MvMass.mass ((IntegralHistorySampler.criticalStep x.sampler (data x hm r)).rows v)≤2^exponent n S B W D L F H := by
      intro v
      cases v with
      | inl i => exact (criticalStep_old_row_mass x.sampler (data x hm r) i).trans (ho i)
      | inr i => exact (new_physical_row x hm r W D L F H hH HG hc ha hw hd hcmd.1 hcmd.2.1 hcmd.2.2 i).trans HC
    exact (scalarStep_row_mass (IntegralHistorySampler.criticalStep x.sampler (data x hm r)) hm
      (criticalPolynomial x hm r) (criticalDegree x hm r) (2^exponent n S B W D L F H) H HI
      (fun u v=>HN.numerator 0 u v) j).trans (max_le le_rfl HR)
  | cut r k d haux hdeg =>
    exact (scalarStep_row_mass x.sampler hm _ _ (2^exponent n S B W D L F H) H ho
      (fun u v=>HN.numerator 0 u v) j).trans (max_le le_rfl HR)

end LeanCanny.Algebra.IntegralMixedPhysicalRowBudget
