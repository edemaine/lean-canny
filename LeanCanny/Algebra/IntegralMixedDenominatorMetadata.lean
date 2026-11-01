/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedDenominatorScript
/-! # Primitive tagged-command fields for mixed denominator evaluation -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedDenominatorScriptBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralMixedHistory IntegralMixedHistoryScript IntegralMixedDenominatorBits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def critical (F : Family) (c : List Bool) (i : ℕ) : Prop :=
  ((commandAt F c i).map Command.isCritical).getD false = true
instance (F : Family) (c : List Bool) (i : ℕ) : Decidable (critical F c i) := inferInstanceAs (Decidable (_ = _))

def offset (F : Family) (c : List Bool) (i : ℕ) : ℕ :=
  match commandAt F c i with
  | some (.critical r) => r.offset.val
  | _ => 0

noncomputable def integerLeading (F : Family) (c : List Bool) (i : ℕ) : ℤ :=
  match commandAt F c i with
  | some (.integer p _ _) => p.leadingCoeff
  | _ => 0

def scale (F : Family) (c : List Bool) (i j : ℕ) : ℤ :=
  match commandAt F c i with
  | some (.critical r) => if hj : j < F.ambient c + 1 then r.scales ⟨j, hj⟩ else 1
  | _ => 1

def scaleProduct (F : Family) (c : List Bool) (i : ℕ) : ℤ := ∏ j ∈ Finset.range (F.ambient c + 1), scale F c i j

theorem scaleProduct_critical (F : Family) (c : List Bool) (i : ℕ) (r : CriticalRule (F.ambient c))
    (h : commandAt F c i = some (.critical r)) : scaleProduct F c i = ∏ j, r.scales j := by
  unfold scaleProduct
  rw [Finset.prod_range]
  apply Finset.prod_congr rfl
  intro j _
  unfold scale
  rw [h]
  dsimp only
  rw [dite_eq_left j.isLt]

theorem offset_le (F : Family) (c : List Bool) (i : ℕ) : offset F c i ≤ F.ambient c := by
  unfold offset
  cases h : commandAt F c i with
  | none => exact Nat.zero_le _
  | some cmd => cases cmd with
    | integer _ _ _ => exact Nat.zero_le _
    | critical r => exact Nat.le_of_lt_succ r.offset.isLt

theorem descriptor_arity (F : Family) (c : List Bool) (i : ℕ) :
    (descriptorAt F c i).arity = if critical F c i then min i (count F c) * (F.ambient c + 1) else 0 := by
  cases h : commandAt F c i with
  | none => simp only [descriptorAt, critical, h, Option.map_none, Option.getD_none, Bool.false_eq_true, ite_false]
  | some cmd => cases cmd <;> simp only [descriptorAt, critical, h, Option.map_some, Option.getD_some, Command.isCritical, instruction, Bool.false_eq_true, ite_false, ite_true]

theorem descriptor_degree (F : Family) (c : List Bool) (i : ℕ) :
    (descriptorAt F c i).degree = if critical F c i then (F.spatial c).degree else 1 := by
  cases h : commandAt F c i with
  | none => simp only [descriptorAt, critical, h, Option.map_none, Option.getD_none, Bool.false_eq_true, ite_false]
  | some cmd => cases cmd <;> simp only [descriptorAt, critical, h, Option.map_some, Option.getD_some, Command.isCritical, instruction, Bool.false_eq_true, ite_false, ite_true]

theorem descriptor_exponent (F : Family) (c : List Bool) (i : ℕ) :
    (descriptorAt F c i).exponent = if critical F c i then
      (PurePowerReductionBounds.bound (F.ambient c - offset F c i + 1) (F.spatial c).degree + 1) *
        PurePowerReductionBounds.dimension (F.ambient c - offset F c i + 1) (F.spatial c).degree else 1 := by
  cases h : commandAt F c i with
  | none => simp only [descriptorAt, critical, h, Option.map_none, Option.getD_none, Bool.false_eq_true, ite_false]
  | some cmd => cases cmd <;> simp only [descriptorAt, critical, offset, h, Option.map_some, Option.getD_some, Command.isCritical, instruction, criticalExponent, Bool.false_eq_true, ite_false, ite_true]

theorem descriptor_index (F : Family) (c : List Bool) (i j : ℕ) :
    (descriptorAt F c i).index j = if critical F c i then j / (F.ambient c + 1) else 0 := by
  cases h : commandAt F c i with
  | none => simp only [descriptorAt, critical, h, Option.map_none, Option.getD_none, Bool.false_eq_true, ite_false]
  | some cmd => cases cmd <;> simp only [descriptorAt, critical, h, Option.map_some, Option.getD_some, Command.isCritical, instruction, Bool.false_eq_true, ite_false, ite_true]

theorem descriptor_leading (F : Family) (c : List Bool) (i : ℕ) :
    (descriptorAt F c i).leading = if critical F c i then (F.spatial c).leading * scaleProduct F c i ^ (F.spatial c).degree else integerLeading F c i := by
  cases h : commandAt F c i with
  | none => simp only [descriptorAt, critical, integerLeading, h, Option.map_none, Option.getD_none, Bool.false_eq_true, ite_false]
  | some cmd => cases cmd with
    | integer p _ _ => simp only [descriptorAt, critical, integerLeading, h, Option.map_some, Option.getD_some, Command.isCritical, instruction, Bool.false_eq_true, ite_false]
    | critical r =>
      rw [scaleProduct_critical F c i r h]
      simp only [descriptorAt, critical, h, Option.map_some, Option.getD_some, Command.isCritical, instruction, ite_true]

noncomputable def integerLeadingReader (F : Family) (p : List Bool) : List Bool :=
  residueBits (integerLeading F (pairFst p) (IntegralDenominatorPass.cursor p) : ZMod (F.modulus (pairFst p)))
noncomputable def spatialLeadingReader (F : Family) (c : List Bool) : List Bool :=
  residueBits ((F.spatial c).leading : ZMod (F.modulus c))
noncomputable def scaleAt (F : Family) (p : List Bool) (j : ℕ) : ZMod (F.modulus (pairFst p)) :=
  (scale F (pairFst p) (IntegralDenominatorPass.cursor p) j : ZMod (F.modulus (pairFst p)))
noncomputable def scaleReader (F : Family) (z : List Bool) : List Bool :=
  residueBits (scaleAt F (pairFst z) (Nat.fromBitsLE (pairSnd z)))

structure Access (F : Family) : Prop where
  count : UnaryFn (count F)
  ambient : UnaryFn F.ambient
  modulus : BinaryFn F.modulus
  degree : BinaryFn (fun c => (F.spatial c).degree)
  critical : FPPred (fun p => critical F (pairFst p) (IntegralDenominatorPass.cursor p))
  offset : BinaryFn (fun p => offset F (pairFst p) (IntegralDenominatorPass.cursor p))
  integerLeading : SpaceFunction (integerLeadingReader F)
  spatialLeading : SpaceFunction (spatialLeadingReader F)
  scales : SpaceFunction (scaleReader F)
end LeanCanny.Algebra.IntegralMixedDenominatorScriptBits
