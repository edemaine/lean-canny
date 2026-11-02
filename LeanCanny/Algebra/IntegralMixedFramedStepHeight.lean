/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullScriptHeight
public import LeanCanny.Algebra.IntegralMixedFramedHistoryScript
/-! # Actual source-framed births obey a charged multiplicative bank bound

The source is changed before the literal mixed command is interpreted. The old
bank is unchanged by that reframe. Existing integer, critical and normalized
cut step-height theorems then prove the new bank bound, including limit cuts.
The frontend LOW, leading, degree and command-syntax bounds remain explicit.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedStepHeight
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical

theorem expression_coefficients_mono {C C' : ℕ} (h : C≤C') (a : AffineExpr)
    (ha : a.CoefficientsBound C) : a.CoefficientsBound C' := by
  induction a with
  | constant c => exact ha.trans h
  | reference _ => trivial
  | add a b ia ib => exact ⟨ia ha.1,ib ha.2⟩
  | scale c a ia => exact ⟨ha.1.trans h,ia ha.2⟩

theorem command_bounds_mono {n B C C' L : ℕ} {P : SpatialSource n} (h : C≤C')
    (c : IntegralMixedFullHistoryScript.Command P B) (hc : IntegralMixedFullScriptHeight.CommandBounds C L c) :
    IntegralMixedFullScriptHeight.CommandBounds C' L c := by
  cases c with
  | integer p hp hd => exact fun k => (hc k).trans (Nat.pow_le_pow_right (by decide) h)
  | critical r => exact ⟨hc.1,fun i => expression_coefficients_mono h _ (hc.2.1 i),fun i => (hc.2.2 i).trans h⟩
  | cut r k d ha hd =>
    exact ⟨hc.1,fun i => expression_coefficients_mono h _ (hc.2.1 i),
      (fun i => (hc.2.2.1 i).trans h),hc.2.2.2.trans h⟩

/-- The stage exponent is F*G. Its source coefficient budget includes one bit
for the sum of the old LOW and the appended power coefficient. -/
structure InstructionBounds {n B : ℕ} (G F W D L : ℕ) (c : Instruction n B) : Prop where
  low : ∀ e, (c.source.low.coeff e).natAbs≤2^(F*G+1)
  leading : c.source.leading.natAbs.size≤F*G+1
  width : c.source.degree.size≤W
  degree : c.source.degree≤D
  auxiliary : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) c.source.degree≤2^B
  command : IntegralMixedFullScriptHeight.CommandBounds (F*G+1) L c.command

def growth (n S B W D L F : ℕ) : ℕ := IntegralMixedFullScriptHeight.growth n S B W D L*(F+2)

theorem growth_pos (n S B W D L F : ℕ) : 1≤growth n S B W D L F := by
  have H := IntegralMixedFullScriptHeight.growth_pos n S B W D L
  unfold growth
  nlinarith

theorem step_bounds {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (c : Instruction n B) (G F W D L : ℕ)
    (HG : x.bank.Bounds G) (hG : 1≤G) (hc : InstructionBounds G F W D L c) :
    (IntegralMixedFullHistoryScript.step (reframe x c.source c.source_cap) hm c.command).bank.Bounds
      (growth n S B W D L F*G) := by
  have Hbank : (reframe x c.source c.source_cap).bank.Bounds ((F+2)*G) :=
    HG.mono (by nlinarith)
  have H := IntegralMixedFullScriptHeight.step_bounds (reframe x c.source c.source_cap) hm c.command
    ((F+2)*G) (F*G+1) W D L Hbank hc.low hc.leading hc.width hc.degree hc.auxiliary hc.command (by nlinarith)
  simpa only [growth,Nat.mul_assoc] using H

end LeanCanny.Algebra.IntegralMixedFramedStepHeight
