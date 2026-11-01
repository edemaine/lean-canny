/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedExpressionBounds
public import LeanCanny.Algebra.IntegralHistoryGlobalHeightBounds
/-! # One original-spatial height ceiling for mixed affine histories

The spatial degree is fixed before any scalar birth. Expression syntax and
one retained-rank cap multiply the logarithmic height budget at each step.
No later norm degree is substituted into the original spatial metadata.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGlobalHeightBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial UniformIntegralPrefix
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def expressionFactor (S L : ℕ) : ℕ := (L + 1) * (S + 3)
def coefficientFactor (n M W D S L : ℕ) : ℕ :=
  IntegralHistoryGlobalHeightBounds.criticalFactor (n + 1) M W D * expressionFactor S L + 1
def growth (n M W D N S L : ℕ) : ℕ := bankGrowth M N (coefficientFactor n M W D S L)
def height (n M W D N S L C j : ℕ) : ℕ := growth n M W D N S L ^ j * (C + 1)

theorem expressionFactor_pos (S L : ℕ) : 1 ≤ expressionFactor S L := by
  unfold expressionFactor
  nlinarith

theorem height_pos (n M W D N S L C j : ℕ) : 1 ≤ height n M W D N S L C j := by
  exact Nat.mul_pos (pow_pos (bankGrowth_pos _ _ _) _) (Nat.succ_pos C)

theorem source_le_height (n M W D N S L C j : ℕ) : C + 1 ≤ height n M W D N S L C j := by
  have H : 1 ≤ growth n M W D N S L ^ j :=
    Nat.one_le_pow _ _ (bankGrowth_pos M N (coefficientFactor n M W D S L))
  simpa only [Nat.one_mul, height] using Nat.mul_le_mul_right (C + 1) H

theorem height_step (n M W D N S L C j : ℕ) :
    height n M W D N S L C (j + 1) = growth n M W D N S L * height n M W D N S L C j := by
  unfold height
  rw [pow_succ']
  exact Nat.mul_assoc _ _ _

theorem expression_height_scaled (a : AffineExpr) (m S L C G : ℕ)
    (hm : m ≤ S) (hL : a.nodes ≤ L) (hC : a.CoefficientsBound C) (hG : C + 1 ≤ G) :
    a.height m G ≤ expressionFactor S L * G := by
  have HA := a.height_le m G C hC
  have HT : (m + 1) * G + C + 1 ≤ (S + 3) * G := by nlinarith
  exact HA.trans ((Nat.mul_le_mul hL HT).trans (by unfold expressionFactor; nlinarith))

theorem retainedBudget_scaled {n : ℕ} (r : CriticalRule n) (m S L C G : ℕ)
    (hm : m ≤ S) (hL : ∀ i, (r.heights i).nodes ≤ L)
    (hC : ∀ i, (r.heights i).CoefficientsBound C) (hG : C + 1 ≤ G) :
    retainedBudget m G r ≤ expressionFactor S L * G := by
  apply Finset.sup_le
  intro i _
  exact expression_height_scaled _ _ _ _ _ _ hm (hL i) (hC i) hG

theorem scaleBudget_le {n : ℕ} (r : CriticalRule n) (C : ℕ)
    (hC : ∀ i, (r.scales i).natAbs.size ≤ C) : scaleBudget r ≤ C := by
  exact Finset.sup_le (fun i _ => hC i)

theorem criticalHeight_scaled {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) (G C M W D L : ℕ)
    (HG : x.bank.Bounds G) (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C)
    (HP : P.leading.natAbs.size ≤ C) (hM : count m B ≤ M) (hW : P.degree.size ≤ W) (hD : P.degree ≤ D)
    (hL : ∀ i, (r.heights i).nodes ≤ L) (hE : ∀ i, (r.heights i).CoefficientsBound C)
    (hScale : ∀ i, (r.scales i).natAbs.size ≤ C) (hG : C + 1 ≤ G) :
    criticalHeight x hm r G C HG HC ≤ coefficientFactor n M W D S L * G := by
  let T := expressionFactor S L * G
  have HT : G ≤ T := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right G (expressionFactor_pos S L)
  have HS : m * G + scaleBudget r ≤ T := by
    have HB := scaleBudget_le r C hScale
    have HF := expressionFactor_pos S L
    have HE : S + 1 ≤ expressionFactor S L := by unfold expressionFactor; nlinarith
    dsimp only [T]
    nlinarith
  have HB := IntegralHistoryCriticalBits.budget_scaled (family x hm r) (familyBounds x hm r G C HG HC)
    [] T (by dsimp only [T]; nlinarith [expressionFactor_pos S L])
    ((Nat.le_succ C).trans (hG.trans HT))
    (retainedBudget_scaled r m S L C G hm hL hE hG) HS
    (HP.trans ((Nat.le_succ C).trans (hG.trans HT)))
  have HF := IntegralHistoryGlobalHeightBounds.heightFactor_le (family x hm r) [] (n + 1) M W D
    (Nat.le_refl _) hM hW hD
  exact HB.trans ((Nat.mul_le_mul_right T HF).trans (by
    dsimp only [T]
    unfold coefficientFactor
    nlinarith))

theorem criticalStep_scaled_bounds {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) (G C M W D L : ℕ)
    (HG : x.bank.Bounds G) (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C)
    (HP : P.leading.natAbs.size ≤ C) (hM : count m B ≤ M) (hW : P.degree.size ≤ W) (hD : P.degree ≤ D)
    (hL : ∀ i, (r.heights i).nodes ≤ L) (hE : ∀ i, (r.heights i).CoefficientsBound C)
    (hScale : ∀ i, (r.scales i).natAbs.size ≤ C) (hG : C + 1 ≤ G) :
    (criticalStep x hm r).bank.Bounds (growth n M W D (2 ^ B) S L * G) := by
  let H := familyBounds x hm r G C HG HC
  have HE := IntegralHistoryCriticalBits.coefficient_height (family x hm r) H []
  exact x.bank.rootStep_scaled_bounds hm _ _ _ G M (coefficientFactor n M W D S L) _ HG
    (by omega) hM (criticalHeight_scaled x hm r G C M W D L HG HC HP hM hW hD hL hE hScale hG)
    HE (IntegralClearedCriticalLeadingBits.integer_height (IntegralHistoryCriticalBits.source (family x hm r)) [] _ HE)

theorem integerStep_scaled_bounds {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (p : Polynomial ℤ) (hp : p ≠ 0) (hcap : p.natDegree ≤ 2 ^ B)
    (G C M W D L : ℕ) (HG : x.bank.Bounds G) (HC : ∀ k, (p.coeff k).natAbs ≤ 2 ^ C)
    (hM : count m B ≤ M) (hG : C + 1 ≤ G) :
    (integerStep x hm p hp hcap).bank.Bounds (growth n M W D (2 ^ B) S L * G) := by
  have HK : 1 ≤ coefficientFactor n M W D S L := by unfold coefficientFactor; omega
  have HKG : G ≤ coefficientFactor n M W D S L * G := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right G HK
  apply x.bank.rootStep_scaled_bounds hm _ _ C G M (coefficientFactor n M W D S L) _ HG (by omega) hM
    ((Nat.le_succ C).trans (hG.trans HKG))
  · intro k r t
    rw [Polynomial.coeff_map]
    exact IntegralHistoryCriticalBits.integer_entry_height _ _ _ (HC k) r t
  · exact HC p.natDegree

end LeanCanny.Algebra.IntegralMixedGlobalHeightBounds
