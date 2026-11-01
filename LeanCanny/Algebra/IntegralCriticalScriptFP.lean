/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalScript

/-! # Native instruction access from original critical-command metadata

Chronological lookup reads the reversed command list. Only the original
leading residue, degree, offset, and old-selector fields are supplied.
The canonical reduction exponent is constructed internally, and missing
commands and coordinates have total numeric defaults.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalScriptFP
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n W D C : ℕ}

theorem instructions_reverse (rules : List (Command n W D C)) :
    instructions rules = rules.reverse.mapIdx (fun i r => r.instruction i) := by
  induction rules with
  | nil => rfl
  | cons r rs ih =>
    rw [instructions, List.reverse_cons, List.mapIdx_concat, ← ih, List.length_reverse]

theorem instructionAt_eq (rules : List (Command n W D C)) (i : ℕ) :
    IntegralCriticalDenominatorScript.instructionAt (instructions rules) i =
      ((rules.reverse[i]?).map (fun r => r.instruction i)).getD ⟨0, 0, 0, []⟩ := by
  unfold IntegralCriticalDenominatorScript.instructionAt
  rw [instructions_reverse, List.getElem?_mapIdx]

structure Family where
  ambient : List Bool → ℕ
  sourceWidth : List Bool → ℕ
  degreeBound : List Bool → ℕ
  height : List Bool → ℕ
  rules : ∀ c, List (Command (ambient c) (sourceWidth c) (degreeBound c) (height c))
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0

def commandAt (F : Family) (c : List Bool) (i : ℕ) := (F.rules c).reverse[i]?
def leading (F : Family) (c : List Bool) (i : ℕ) := ((commandAt F c i).map Command.leading).getD 0
def degree (F : Family) (c : List Bool) (i : ℕ) := ((commandAt F c i).map Command.degree).getD 0
def offset (F : Family) (c : List Bool) (i : ℕ) := ((commandAt F c i).map (fun r => r.offset.val)).getD 0

def selector (F : Family) (c : List Bool) (i j : ℕ) :=
  match commandAt F c i with
  | none => i
  | some r => if h : j < F.ambient c + 1 then r.selected ⟨j, h⟩ else i

def free (F : Family) (c : List Bool) (i : ℕ) := F.ambient c - offset F c i + 1

def program (F : Family) :=
  IntegralCriticalDenominatorScript.program (fun c => instructions (F.rules c)) F.modulus F.modulus_ne_zero

def valid (F : Family) (p : List Bool) : Prop := IntegralDenominatorPass.cursor p < (F.rules (pairFst p)).length
instance (F : Family) (p : List Bool) : Decidable (valid F p) := inferInstanceAs (Decidable (_ < _))

structure Access (F : Family) : Prop where
  count : UnaryFn (fun c => (F.rules c).length)
  ambient : UnaryFn F.ambient
  modulus : BinaryFn F.modulus
  leading : (fun p => residueBits (leading F (pairFst p) (IntegralDenominatorPass.cursor p) : ZMod (F.modulus (pairFst p)))) ∈ FP
  degree : BinaryFn (fun p => degree F (pairFst p) (IntegralDenominatorPass.cursor p))
  offset : BinaryFn (fun p => offset F (pairFst p) (IntegralDenominatorPass.cursor p))
  selector : BinaryFn (fun z => selector F (pairFst (pairFst z)) (IntegralDenominatorPass.cursor (pairFst z)) (Nat.fromBitsLE (pairSnd z)))

theorem cursor_binary : BinaryFn IntegralDenominatorPass.cursor :=
  BinaryFn.fromBits BoundedFold.counter_mem_FP

theorem valid_FP (F : Family) (a : Access F) : FPPred (valid F) :=
  cursor_binary.lt ((BinaryFn.ofUnary a.count).comp pairFst_mem_FP)

theorem commandAt_none (F : Family) (c : List Bool) (i : ℕ) (hi : (F.rules c).length ≤ i) : commandAt F c i = none := by
  apply List.getElem?_eq_none
  simpa only [List.length_reverse] using hi

theorem commandAt_some_lt (F : Family) (c : List Bool) (i : ℕ) (r : Command (F.ambient c) (F.sourceWidth c) (F.degreeBound c) (F.height c))
    (hr : commandAt F c i = some r) : i < (F.rules c).length := by
  by_contra h
  rw [commandAt_none F c i (by omega)] at hr
  cases hr

theorem commandAt_ne_none (F : Family) (c : List Bool) (i : ℕ) (hi : i < (F.rules c).length) : commandAt F c i ≠ none := by
  unfold commandAt
  rw [List.getElem?_eq_getElem (by simpa only [List.length_reverse] using hi)]
  exact Option.some_ne_none _

theorem program_leading (F : Family) (c : List Bool) (i : ℕ) : (program F).leading c i = leading F c i := by
  change (IntegralCriticalDenominatorScript.instructionAt (instructions (F.rules c)) i).leading = _
  rw [instructionAt_eq]
  unfold leading commandAt
  cases (F.rules c).reverse[i]? <;> rfl

theorem program_degree (F : Family) (c : List Bool) (i : ℕ) : (program F).degree c i = degree F c i := by
  change (IntegralCriticalDenominatorScript.instructionAt (instructions (F.rules c)) i).degree = _
  rw [instructionAt_eq]
  unfold degree commandAt
  cases (F.rules c).reverse[i]? <;> rfl

theorem offset_le (F : Family) (c : List Bool) (i : ℕ) : offset F c i ≤ F.ambient c := by
  unfold offset
  cases hr : commandAt F c i with
  | none => exact Nat.zero_le _
  | some r => exact Nat.le_of_lt_succ r.offset.isLt

theorem program_arity (F : Family) (c : List Bool) (i : ℕ) :
    (program F).arity c i = if i < (F.rules c).length then F.ambient c + 1 else 0 := by
  change (IntegralCriticalDenominatorScript.instructionAt (instructions (F.rules c)) i).indices.length = _
  rw [instructionAt_eq]
  change (((commandAt F c i).map (fun (r : Command (F.ambient c) (F.sourceWidth c) (F.degreeBound c) (F.height c)) => r.instruction i)).getD (⟨0, 0, 0, []⟩ : IntegralCriticalDenominatorScript.Instruction)).indices.length = _
  cases hr : commandAt F c i with
  | none => rw [ite_eq_right (by intro hi; exact commandAt_ne_none F c i hi hr)]; rfl
  | some r => rw [ite_eq_left (commandAt_some_lt F c i r hr)]; exact List.length_ofFn

theorem program_exponent (F : Family) (c : List Bool) (i : ℕ) :
    (program F).exponent c i = if i < (F.rules c).length then
      (PurePowerReductionBounds.bound (free F c i) (degree F c i) + 1) *
        PurePowerReductionBounds.dimension (free F c i) (degree F c i) else 0 := by
  change (IntegralCriticalDenominatorScript.instructionAt (instructions (F.rules c)) i).exponent = _
  rw [instructionAt_eq]
  change (((commandAt F c i).map (fun (r : Command (F.ambient c) (F.sourceWidth c) (F.degreeBound c) (F.height c)) => r.instruction i)).getD (⟨0, 0, 0, []⟩ : IntegralCriticalDenominatorScript.Instruction)).exponent = _
  cases hr : commandAt F c i with
  | none => rw [ite_eq_right (by intro hi; exact commandAt_ne_none F c i hi hr)]; rfl
  | some r =>
    rw [ite_eq_left (commandAt_some_lt F c i r hr)]
    simp only [free, offset, degree, hr, Option.map_some, Option.getD_some]
    rfl

theorem program_index (F : Family) (c : List Bool) (i j : ℕ) :
    (program F).index c i j = min (selector F c i j) i := by
  change ((IntegralCriticalDenominatorScript.instructionAt (instructions (F.rules c)) i).indices[j]?).getD i = _
  rw [instructionAt_eq]
  change ((((commandAt F c i).map (fun (r : Command (F.ambient c) (F.sourceWidth c) (F.degreeBound c) (F.height c)) => r.instruction i)).getD (⟨0, 0, 0, []⟩ : IntegralCriticalDenominatorScript.Instruction)).indices[j]?).getD i = _
  unfold selector
  cases hr : commandAt F c i with
  | none => exact (min_self i).symm
  | some r =>
    simp only [Option.map_some, Option.getD_some, Command.instruction, List.getElem?_ofFn]
    by_cases hj : j < F.ambient c + 1
    · rw [dite_eq_left hj, dite_eq_left hj, Option.getD_some]
      split_ifs <;> omega
    · rw [dite_eq_right hj, dite_eq_right hj, Option.getD_none, min_self]

theorem offset_unary (F : Family) (a : Access F) :
    UnaryFn (fun p => offset F (pairFst p) (IntegralDenominatorPass.cursor p)) :=
  (UnaryFn.fromBitsLE_of_le a.offset.bits_mem_FP (a.ambient.comp pairFst_mem_FP)
    (fun p => by rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact offset_le F _ _)).of_eq
    (fun _ => Nat.fromBitsLE_bits _)

theorem free_unary (F : Family) (a : Access F) :
    UnaryFn (fun p => free F (pairFst p) (IntegralDenominatorPass.cursor p)) :=
  ((a.ambient.comp pairFst_mem_FP).sub (offset_unary F a)).add (UnaryFn.const 1)

theorem exponent_binary (F : Family) (a : Access F) :
    BinaryFn (fun p => (program F).exponent (pairFst p) (IntegralDenominatorPass.cursor p)) := by
  have HF := free_unary F a
  have HB := (PurePowerReductionBounds.bound_binary (BinaryFn.ofUnary HF) a.degree).add (BinaryFn.const 1)
  have HE := HB.mul (PurePowerReductionBounds.dimension_binary HF a.degree)
  exact (BinaryFn.ite (valid_FP F a) HE (BinaryFn.const 0)).of_eq
    (fun p => (program_exponent F (pairFst p) (IntegralDenominatorPass.cursor p)).symm)

theorem access (F : Family) (a : Access F) : IntegralDenominatorPass.Access (program F) where
  count := a.count.of_eq (fun c => (instructions_length (F.rules c)).symm)
  modulus := a.modulus
  arity := by
    have H : UnaryFn (fun p => if valid F p then F.ambient (pairFst p) + 1 else 0) :=
      (valid_FP F a).computable.ite_decide ((a.ambient.comp pairFst_mem_FP).add (UnaryFn.const 1)) (UnaryFn.const 0)
    exact H.of_eq (fun p => (program_arity F (pairFst p) (IntegralDenominatorPass.cursor p)).symm)
  leading := mem_FP_of_eq a.leading (fun p => by rw [program_leading])
  degree := a.degree.of_eq (fun p => (program_degree F (pairFst p) (IntegralDenominatorPass.cursor p)).symm)
  exponent := exponent_binary F a
  index := by
    have HI : BinaryFn (fun z => IntegralDenominatorPass.cursor (pairFst z)) := cursor_binary.comp pairFst_mem_FP
    have H := BinaryFn.ite (a.selector.le HI) a.selector HI
    exact H.of_eq (fun z => by
      rw [program_index, Nat.min_def])

end LeanCanny.Algebra.IntegralCriticalScriptFP
