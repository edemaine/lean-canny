/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCutStepHeight
public import LeanCanny.Algebra.IntegralMixedFullHistoryPrefix
public import LeanCanny.Algebra.IntegralMixedGlobalHeightControls
/-! # One multiplicative height ceiling includes every full-history command -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullScriptHeight
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial UniformIntegralPrefix
open IntegralMixedHistory IntegralMixedFullHistoryScript
set_option backward.isDefEq.respectTransparency false

def rank (S B : ℕ) := count (S + 2) B
def cutFactor (n S B W D L : ℕ) := IntegralMixedCutBounds.normalizedHeight (rank S B)
  (IntegralMixedCutHeightProfile.factor n (rank S B) W D S L)
def coefficientFactor (n S B W D L : ℕ) :=
  max (IntegralMixedGlobalHeightBounds.coefficientFactor n (rank S B) W D S L) (cutFactor n S B W D L) + 1
def growth (n S B W D L : ℕ) := bankGrowth (rank S B) (2 ^ B) (coefficientFactor n S B W D L)
def height (n S B W D L C j : ℕ) := growth n S B W D L ^ j * (C + 1)

def CommandBounds {n B : ℕ} {P : SpatialSource n} (C L : ℕ) : Command P B → Prop
  | .integer p _ _ => ∀ k, (p.coeff k).natAbs ≤ 2 ^ C
  | .critical r => (∀ i, (r.heights i).nodes ≤ L) ∧ (∀ i, (r.heights i).CoefficientsBound C) ∧
      (∀ i, (r.scales i).natAbs.size ≤ C)
  | .cut r _ _ _ _ => (∀ i, (r.critical.heights i).nodes ≤ L) ∧ (∀ i, (r.critical.heights i).CoefficientsBound C) ∧
      (∀ i, (r.critical.scales i).natAbs.size ≤ C) ∧ r.slope.natAbs.size ≤ C

theorem growth_pos (n S B W D L : ℕ) : 1 ≤ growth n S B W D L := bankGrowth_pos _ _ _
theorem source_le_height (n S B W D L C j : ℕ) : C + 1 ≤ height n S B W D L C j := by
  have H : 1 ≤ growth n S B W D L ^ j := Nat.one_le_pow _ _ (growth_pos n S B W D L)
  simpa only [Nat.one_mul, height] using Nat.mul_le_mul_right (C + 1) H
theorem height_pos (n S B W D L C j : ℕ) : 1 ≤ height n S B W D L C j := (Nat.succ_pos C).trans_le (source_le_height _ _ _ _ _ _ _ _)
theorem height_step (n S B W D L C j : ℕ) :
    height n S B W D L C (j + 1) = growth n S B W D L * height n S B W D L C j := by
  unfold height
  rw [pow_succ']
  exact Nat.mul_assoc _ _ _

theorem legacy_growth_le (n S B W D L : ℕ) :
    IntegralMixedGlobalHeightBounds.growth n (rank S B) W D (2 ^ B) S L ≤ growth n S B W D L := by
  have H : IntegralMixedGlobalHeightBounds.coefficientFactor n (rank S B) W D S L ≤ coefficientFactor n S B W D L :=
    (le_max_left _ _).trans (Nat.le_succ _)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right H 1)) 1

theorem cut_growth_le (n S B W D L : ℕ) : bankGrowth (rank S B) (2 ^ B) (cutFactor n S B W D L) ≤ growth n S B W D L := by
  have H : cutFactor n S B W D L ≤ coefficientFactor n S B W D L := (le_max_right _ _).trans (Nat.le_succ _)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right H 1)) 1

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem step_bounds (x : State P S B m ι) (hm : m ≤ S) (c : Command P B) (G C W D L : ℕ)
    (HG : x.bank.Bounds G) (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C) (HP : P.leading.natAbs.size ≤ C)
    (hW : P.degree.size ≤ W) (hD : P.degree ≤ D)
    (hB : IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) P.degree ≤ 2 ^ B)
    (hc : CommandBounds C L c) (hG : C + 1 ≤ G) :
    (IntegralMixedFullHistoryScript.step x hm c).bank.Bounds (growth n S B W D L * G) := by
  have HR : count m B ≤ rank S B := Nat.pow_le_pow_right (Nat.two_pow_pos B) (by omega : m ≤ S + 2)
  have HA : count (m + 2) B ≤ rank S B := Nat.pow_le_pow_right (Nat.two_pow_pos B) (by omega : m + 2 ≤ S + 2)
  cases c with
  | integer p hp hd =>
    exact (IntegralMixedGlobalHeightBounds.integerStep_scaled_bounds x hm p hp hd G C (rank S B) W D L HG hc HR hG).mono
      (Nat.mul_le_mul_right G (legacy_growth_le n S B W D L))
  | critical r =>
    exact (IntegralMixedGlobalHeightBounds.criticalStep_scaled_bounds x hm r G C (rank S B) W D L HG HC HP HR hW hD hc.1 hc.2.1 hc.2.2 hG).mono
      (Nat.mul_le_mul_right G (legacy_growth_le n S B W D L))
  | cut r k d ha hd =>
    exact (IntegralMixedCutStepHeight.step_bounds x hm r k d ha hB G C (rank S B) W D L HG HC HP HA hW hD hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hG).mono
      (Nat.mul_le_mul_right G (cut_growth_le n S B W D L))
end LeanCanny.Algebra.IntegralMixedFullScriptHeight
