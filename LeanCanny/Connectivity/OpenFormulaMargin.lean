/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaStrictWitness
/-! # A continuous nonnegative margin for actual strict-positive Boolean formulas -/
@[expose] public section
namespace LeanCanny.Connectivity.OpenFormulaMargin
open ETR

inductive Open : Formula → Prop where
  | falsum : Open .falsum
  | verum : Open (.not .falsum)
  | ltZero (t : Term) : Open (.ltZero t)
  | and {p q} : Open p → Open q → Open (.and p q)
  | or {p q} : Open p → Open q → Open (.or p q)

noncomputable def margin (env : ℕ → ℝ) : Formula → ℝ
  | .not .falsum => 1
  | .ltZero t => max (-t.eval env) 0
  | .and p q => margin env p*margin env q
  | .or p q => margin env p+margin env q
  | _ => 0

theorem nonneg {p : Formula} (hp : Open p) (env : ℕ → ℝ) : 0≤margin env p := by
  induction hp with
  | falsum => exact le_rfl
  | verum => exact zero_le_one
  | ltZero t => exact le_max_right _ _
  | and _ _ HP HQ => exact mul_nonneg HP HQ
  | or _ _ HP HQ => exact add_nonneg HP HQ

theorem mul_pos_iff {a b : ℝ} (ha : 0≤a) (hb : 0≤b) : 0<a*b ↔ 0<a ∧ 0<b := by
  constructor
  · intro H
    have HA : 0<a := by
      by_contra HN
      have HE : a=0 := le_antisymm (le_of_not_gt HN) ha
      rw [HE,zero_mul] at H
      exact (lt_irrefl _ H)
    have HB : 0<b := by
      by_contra HN
      have HE : b=0 := le_antisymm (le_of_not_gt HN) hb
      rw [HE,mul_zero] at H
      exact (lt_irrefl _ H)
    exact ⟨HA,HB⟩
  · exact fun H => mul_pos H.1 H.2

theorem add_pos_iff {a b : ℝ} (ha : 0≤a) (hb : 0≤b) : 0<a+b ↔ 0<a ∨ 0<b := by
  constructor
  · intro H
    by_cases HA : 0<a
    · exact Or.inl HA
    · have HE : a=0 := le_antisymm (le_of_not_gt HA) ha
      rw [HE,zero_add] at H
      exact Or.inr H
  · rintro (H | H)
    · exact add_pos_of_pos_of_nonneg H hb
    · exact add_pos_of_nonneg_of_pos ha H

theorem positive_iff {p : Formula} (hp : Open p) (env : ℕ → ℝ) : 0<margin env p ↔ p.Holds env := by
  induction hp with
  | falsum => simp only [margin,Formula.Holds,lt_self_iff_false]
  | verum => simp [margin,Formula.Holds]
  | ltZero t => simp only [margin,lt_max_iff,lt_self_iff_false,or_false,neg_pos,Formula.Holds]
  | and hp hq HP HQ => exact (mul_pos_iff (nonneg hp env) (nonneg hq env)).trans (and_congr HP HQ)
  | or hp hq HP HQ => exact (add_pos_iff (nonneg hp env) (nonneg hq env)).trans (or_congr HP HQ)

theorem continuous_margin {p : Formula} (hp : Open p) (n : ℕ) :
    Continuous (fun x : Fin n → ℝ => margin (Formula.extend x) p) := by
  induction hp with
  | falsum => exact continuous_const
  | verum => exact continuous_const
  | ltZero t => exact (FormulaStrictWitness.continuous_eval n t).neg.max continuous_const
  | and _ _ HP HQ => exact HP.mul HQ
  | or _ _ HP HQ => exact HP.add HQ

end LeanCanny.Connectivity.OpenFormulaMargin
