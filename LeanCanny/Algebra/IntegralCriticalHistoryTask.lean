/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalQueryBounds
public import LeanCanny.Algebra.IntegralHistoryGlobalHeightBounds
public import LeanCanny.Encoding.RankedHistoryFields

/-! # One bounded task format for the critical-history stages

The numeric cap includes the full born-prefix rank and the derived uniform
height budget. Its binary length remains polynomial: the height budget,
rather than its exponential coefficient bound, is stored as a number.
Every stage shares sixteen numeric fields and one original root word.
The twenty-seven phases order local requests; retained heights can return
to the companion phase only at a strictly earlier birth.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalHistoryTask
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
set_option backward.isDefEq.respectTransparency false

structure Parameters where
  cap : List Bool → ℕ
  width : List Bool → ℕ
  ambient : List Bool → ℕ
  sourceWidth : List Bool → ℕ
  degree : List Bool → ℕ
  height : List Bool → ℕ
  modulusBound : List Bool → ℕ

structure Access (F : Parameters) : Prop where
  cap : UnaryFn F.cap
  width : UnaryFn F.width
  ambient : UnaryFn F.ambient
  sourceWidth : UnaryFn F.sourceWidth
  degree : BinaryFn F.degree
  height : BinaryFn F.height
  modulusBound : BinaryFn F.modulusBound

def birthCap (F : Parameters) (r : List Bool) : ℕ := F.cap r + 1

def rankCap (F : Parameters) (r : List Bool) : ℕ := count (F.cap r + 1) (F.width r)

def heightBudget (F : Parameters) (r : List Bool) : ℕ :=
  IntegralHistoryGlobalHeightBounds.height (F.ambient r + 1) (count (F.cap r) (F.width r))
    (F.sourceWidth r) (F.degree r) (2 ^ F.width r) (F.height r) (F.cap r + 1)

def numericCap (F : Parameters) (r : List Bool) : ℕ :=
  IntegralCriticalQueryBounds.cap (birthCap F r) (F.ambient r + 1) (rankCap F r)
    (F.sourceWidth r) (F.degree r) (2 ^ F.width r) (heightBudget F r) (F.modulusBound r)

theorem birthCap_unary (F : Parameters) (a : Access F) : UnaryFn (birthCap F) :=
  a.cap.add (UnaryFn.const 1)

theorem rankCap_binary (F : Parameters) (a : Access F) : BinaryFn (rankCap F) :=
  ((BinaryFn.const 2).powUnary a.width).powUnary (birthCap_unary F a)

theorem heightBudget_binary (F : Parameters) (a : Access F) : BinaryFn (heightBudget F) :=
  IntegralHistoryGlobalHeightBounds.uniform_height_binary (a.ambient.add (UnaryFn.const 1))
    a.sourceWidth a.degree a.height a.cap a.width

theorem numericCap_binary (F : Parameters) (a : Access F) : BinaryFn (numericCap F) :=
  IntegralCriticalQueryBounds.cap_binary (BinaryFn.ofUnary (birthCap_unary F a))
    (a.ambient.add (UnaryFn.const 1)) (rankCap_binary F a) a.sourceWidth a.degree
    ((BinaryFn.const 2).powUnary a.width) (heightBudget_binary F a) a.modulusBound

theorem numericCap_pos (F : Parameters) (r : List Bool) : 0 < numericCap F r := by
  exact (Nat.succ_pos _).trans_le (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).1

theorem born_rank_le (F : Parameters) (r : List Bool) {m : ℕ} (hm : m ≤ birthCap F r) :
    count m (F.width r) ≤ numericCap F r :=
  (Nat.pow_le_pow_right (Nat.two_pow_pos _) hm).trans
    (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.1

theorem heightBudget_le (F : Parameters) (r : List Bool) : heightBudget F r ≤ numericCap F r :=
  (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.2.2.2.2.1

/-- These tags name actual local algorithms, in dependency order. -/
inductive Phase where
  | originalCoefficient | derivativeCoefficient | clearedHeight
  | monomialFactor | factorPower | productEntry | productPower
  | originalGridTerm | clearedGridSum | frozenPowerTerm | frozenPowerSum
  | frozenConstant | frozenLower | coordinateGradientProduct | eulerSum
  | eulerObjective | eulerLower | reductionEntry | reductionPower
  | actionEntry | actionPower | momentEntry | momentPower
  | relativeFactor | relativePower | criticalCoefficient | companion
  deriving DecidableEq, Repr

def Phase.code : Phase → ℕ
  | .originalCoefficient => 0 | .derivativeCoefficient => 1 | .clearedHeight => 2
  | .monomialFactor => 3 | .factorPower => 4 | .productEntry => 5 | .productPower => 6
  | .originalGridTerm => 7 | .clearedGridSum => 8 | .frozenPowerTerm => 9
  | .frozenPowerSum => 10 | .frozenConstant => 11 | .frozenLower => 12
  | .coordinateGradientProduct => 13 | .eulerSum => 14 | .eulerObjective => 15
  | .eulerLower => 16 | .reductionEntry => 17 | .reductionPower => 18
  | .actionEntry => 19 | .actionPower => 20 | .momentEntry => 21 | .momentPower => 22
  | .relativeFactor => 23 | .relativePower => 24 | .criticalCoefficient => 25 | .companion => 26

theorem Phase.code_lt (p : Phase) : p.code < 27 := by cases p <;> decide

def phase (q : List Bool) : ℕ := RankedHistoryTask.phase 27 q

def birth (F : Parameters) : List Bool → ℕ := RankedHistoryTask.birth (birthCap F)

def rank (F : Parameters) : List Bool → ℕ := RankedHistoryTask.rank (birthCap F) 27

def isPhase (p : Phase) (q : List Bool) : Prop := phase q = p.code

instance (p : Phase) (q : List Bool) : Decidable (isPhase p q) := inferInstanceAs (Decidable (_ = _))

theorem isPhase_FP (p : Phase) : FPPred (isPhase p) :=
  (BinaryFn.ofUnary (RankedHistoryTask.phase_unary 27)).eq (BinaryFn.const p.code)

/-- Shared slots: stage-specific meanings use the remaining eight positions. -/
inductive Field where
  | modulus | row | col | coefficient | target | expression | derivative | sourceIndex
  | slot8 | slot9 | slot10 | slot11 | slot12 | slot13 | slot14 | slot15
  deriving DecidableEq, Repr

def Field.code : Field → ℕ
  | .modulus => 0 | .row => 1 | .col => 2 | .coefficient => 3
  | .target => 4 | .expression => 5 | .derivative => 6 | .sourceIndex => 7
  | .slot8 => 8 | .slot9 => 9 | .slot10 => 10 | .slot11 => 11
  | .slot12 => 12 | .slot13 => 13 | .slot14 => 14 | .slot15 => 15

theorem Field.code_lt (f : Field) : f.code < 16 := by cases f <;> decide

def get (F : Parameters) (f : Field) (q : List Bool) : ℕ :=
  RankedHistoryFields.get (numericCap F) 16 q f.code

theorem get_binary (F : Parameters) (a : Access F) (f : Field) : BinaryFn (get F f) := by
  have H := BinaryFn.fromBits (mem_FP_comp (mem_FP_pair id_mem_FP (constFn_mem_FP (BinaryNatCode.encode f.code)))
    (RankedHistoryFields.read_FP (numericCap F) 16 (numericCap_binary F a)))
  exact H.of_eq (fun q => by
    dsimp only [Function.comp_apply, id_eq]
    rw [RankedHistoryFields.read_packet, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl)

theorem get_le (F : Parameters) (f : Field) (q : List Bool) :
    get F f q ≤ numericCap F (RankedHistoryTask.root q) := RankedHistoryFields.get_le _ _ _ _

def modulus (F : Parameters) (q : List Bool) : ℕ := if get F .modulus q = 0 then 1 else get F .modulus q

theorem modulus_ne_zero (F : Parameters) (q : List Bool) : modulus F q ≠ 0 := by
  unfold modulus
  split_ifs <;> omega

theorem modulus_binary (F : Parameters) (a : Access F) : BinaryFn (modulus F) :=
  BinaryFn.ite ((get_binary F a .modulus).eq (BinaryFn.const 0)) (BinaryFn.const 1) (get_binary F a .modulus)

def child (F : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ) (p : Phase)
    (reader : List Bool → List Bool) : List Bool → List Bool :=
  RankedHistoryFields.flatten (numericCap F) 16 parent b (fun _ => p.code) reader

theorem child_FP (F : Parameters) (a : Access F) (parent : List Bool → List Bool) (hp : parent ∈ FP)
    (b : List Bool → ℕ) (hb : BinaryFn b) (p : Phase) (reader : List Bool → List Bool) (hr : reader ∈ FP) :
    child F parent b p reader ∈ FP :=
  RankedHistoryFields.flatten_FP _ _ (numericCap_binary F a) parent hp b (fun _ => p.code) hb (BinaryFn.const p.code) reader hr

theorem child_root (F : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ)
    (p : Phase) (reader : List Bool → List Bool) (q : List Bool) :
    RankedHistoryTask.root (child F parent b p reader q) = RankedHistoryTask.root (parent q) :=
  RankedHistoryFields.root_flatten _ _ _ _ _ _ _

theorem child_get (F : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ)
    (p : Phase) (reader : List Bool → List Bool) (q : List Bool) (f : Field) :
    get F f (child F parent b p reader q) =
      min (Nat.fromBitsLE (reader (pair q (BinaryNatCode.encode f.code)))) (numericCap F (RankedHistoryTask.root (parent q))) :=
  RankedHistoryFields.get_flatten _ _ _ _ _ _ _ _ f.code_lt

theorem child_lower_phase (F : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ)
    (p : Phase) (reader : List Bool → List Bool) (q : List Bool)
    (hb : b q = birth F (parent q)) (hp : p.code < phase (parent q)) :
    rank F (child F parent b p reader q) < rank F (parent q) :=
  RankedHistoryFields.flatten_lower_phase _ _ (birthCap F) 27 _ _ _ _ _ hb hp

theorem child_lower_birth (F : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ)
    (p : Phase) (reader : List Bool → List Bool) (q : List Bool)
    (hb : b q < birth F (parent q)) : rank F (child F parent b p reader q) < rank F (parent q) :=
  RankedHistoryFields.flatten_lower_birth _ _ (birthCap F) 27 _ _ _ _ _ hb p.code_lt

def wordBudget (F : Parameters) : List Bool → ℕ :=
  RankedHistoryTask.wordBudget (birthCap F) 27 (RankedHistoryFields.bound (numericCap F) 16)

theorem wordBudget_unary (F : Parameters) (a : Access F) : UnaryFn (wordBudget F) :=
  RankedHistoryFields.wordBudget_unary _ _ (birthCap F) 27 (birthCap_unary F a) (numericCap_binary F a)

theorem child_length (F : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ)
    (p : Phase) (reader : List Bool → List Bool) (q : List Bool)
    (hb : b q ≤ birthCap F (RankedHistoryTask.root (parent q))) :
    (child F parent b p reader q).length ≤ wordBudget F (parent q) :=
  RankedHistoryFields.flatten_length_le _ _ (birthCap F) 27 _ _ _ _ _ hb p.code_lt.le

theorem rank_bound (F : Parameters) (q : List Bool) :
    rank F q < 27 * (F.cap (RankedHistoryTask.root q) + 2) := by
  exact RankedHistoryTask.rank_bound _ _ (by decide) _

/-- The initial word may be malformed and arbitrarily padded. Descendants
use the bounded canonical format and preserve precisely its root record. -/
def Tasks (F : Parameters) (root q : List Bool) : Prop :=
  q = root ∨ (RankedHistoryTask.root q = RankedHistoryTask.root root ∧ q.length ≤ wordBudget F root)

theorem tasks_self (F : Parameters) (q : List Bool) : Tasks F q q := Or.inl rfl

theorem tasks_root (F : Parameters) {r q : List Bool} (h : Tasks F r q) :
    RankedHistoryTask.root q = RankedHistoryTask.root r := by
  rcases h with rfl | h
  · rfl
  · exact h.1

theorem wordBudget_eq (F : Parameters) {r q : List Bool}
    (h : RankedHistoryTask.root q = RankedHistoryTask.root r) : wordBudget F q = wordBudget F r := by
  unfold wordBudget RankedHistoryTask.wordBudget
  rw [h]

theorem child_tasks (F : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ)
    (p : Phase) (reader : List Bool → List Bool) (r q : List Bool) (ht : Tasks F r (parent q))
    (hb : b q ≤ birthCap F (RankedHistoryTask.root (parent q))) :
    Tasks F r (child F parent b p reader q) :=
  Or.inr ⟨(child_root F parent b p reader q).trans (tasks_root F ht),
    (child_length F parent b p reader q hb).trans_eq (wordBudget_eq F (tasks_root F ht))⟩

def taskBudget (F : Parameters) (r : List Bool) : ℕ := r.length + wordBudget F r

theorem tasks_length (F : Parameters) {r q : List Bool} (h : Tasks F r q) : q.length ≤ taskBudget F r := by
  rcases h with rfl | h
  · exact Nat.le_add_right _ _
  · exact h.2.trans (Nat.le_add_left _ _)

theorem taskBudget_unary (F : Parameters) (a : Access F) : UnaryFn (taskBudget F) :=
  (UnaryFn.length id_mem_FP).add (wordBudget_unary F a)

def rankBudget (F : Parameters) (r : List Bool) : ℕ := 27 * (F.cap (RankedHistoryTask.root r) + 2)

theorem rankBudget_unary (F : Parameters) (a : Access F) : UnaryFn (rankBudget F) :=
  (UnaryFn.const 27).mul ((a.cap.comp RankedHistoryTask.root_FP).add (UnaryFn.const 2))

theorem tasks_rank (F : Parameters) {r q : List Bool} (h : Tasks F r q) : rank F q < rankBudget F r := by
  have H := rank_bound F q
  rw [tasks_root F h] at H
  exact H

end LeanCanny.Algebra.IntegralCriticalHistoryTask
