/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalDenominatorScript
public import LeanCanny.Algebra.IntegralDenominatorPrefixFP

/-! # Critical history commands independent of their parameter algebra

Commands store integer source data and indices of older heights. Their
interpretation constructs the actual scalar prefixes and canonical height
banks. The physical schedule and scalar width are fixed for the whole
script. This syntax covers critical births only.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalScript
open LeanCanny.Encoding LeanCanny.Computation UniformIntegralPrefix FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Command (n W D C : ℕ) where
  low : MvPolynomial (Fin (n + 1)) ℤ
  leading : ℤ
  degree : ℕ
  degree_two : 2 ≤ degree
  degree_le : degree ≤ D
  degree_lt : degree < 2 ^ W
  low_degree : low.totalDegree < degree
  leading_ne : leading ≠ 0
  low_height : ∀ e, (low.coeff e).natAbs ≤ 2 ^ C
  leading_height : leading.natAbs ≤ 2 ^ C
  offset : Fin (n + 1)
  objective : ℕ
  coordinate : ℕ
  selected : Fin (n + 1) → ℕ

def Command.select {n W D C : ℕ} (r : Command n W D C) (m : ℕ) (i : Fin (n + 1)) : Option (Fin m) :=
  if h : r.selected i < m then some ⟨r.selected i, h⟩ else none

structure State (S B n W D C m : ℕ) where
  scalarPrefix : Prefix S (2 ^ B) m
  bank : HeightBank scalarPrefix
  history : IntegralScalarRootHistoryBounds.History (n + 1) W D C scalarPrefix bank

variable {S B n W D C m : ℕ}

noncomputable def base (S B n W D C : ℕ) : State S B n W D C 0 where
  scalarPrefix := UniformIntegralPrefix.base S (2 ^ B)
  bank := HeightBank.base S B
  history := .base S B

noncomputable def data (x : State S B n W D C m) (hm : m ≤ S) (r : Command n W D C) :
    IntegralHistorySampler.CriticalData x.scalarPrefix n where
  heights i := x.bank.selectedNumerator (r.select m i)
  low := r.low
  leading := r.leading
  objective := 1
  scales i := x.bank.selectedDenominator (r.select m i)
  frozen := Finset.univ.filter (fun i => i.val < r.offset.val)
  free := r.offset
  degree := r.degree
  birth_bound := hm
  degree_two := r.degree_two
  low_degree := r.low_degree
  leading_ne := r.leading_ne
  objective_ne := by decide
  scales_ne i := by
    cases h : r.select m i with
    | none => change (1 : ℤ) ≠ 0; decide
    | some j => exact x.history.denominators_ne_zero j
  free_not_frozen := by simp

noncomputable def family (x : State S B n W D C m) (hm : m ≤ S) (r : Command n W D C) : IntegralHistoryCriticalBits.Family where
  cap _ := S
  width _ := B
  birth _ := m
  ambient _ := n
  free _ := n - r.offset.val
  scalarPrefix _ := x.scalarPrefix
  data _ := data x hm r
  offset _ := r.offset.val
  fit _ := by have := r.offset.isLt; omega
  sourceWidth _ := W
  degree_lt _ := r.degree_lt
  objective _ := ⟨r.objective % (n - r.offset.val + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  coordinate _ := ⟨r.coordinate % (n - r.offset.val + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  coefficientIndex _ := 0
  target _ := 0
  row _ := ⟨0, by change 0 < (2 ^ B) ^ m; exact pow_pos (Nat.two_pow_pos B) m⟩
  col _ := ⟨0, by change 0 < (2 ^ B) ^ m; exact pow_pos (Nat.two_pow_pos B) m⟩
  modulus _ := 1
  modulus_ne_zero _ := by decide

theorem degree_le (x : State S B n W D C m) (hm : m ≤ S) (r : Command n W D C)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) :
    IntegralScalarRootHistoryBounds.degree (family x hm r) [] ≤ 2 ^ B := by
  change PurePowerReductionBounds.dimension (n - r.offset.val + 1) r.degree ≤ 2 ^ B
  exact (IntegralCriticalFactorCeiling.dimension_mono (by omega : n - r.offset.val + 1 ≤ n + 1) r.degree_le).trans hN

noncomputable def step (x : State S B n W D C m) (hm : m ≤ S) (r : Command n W D C)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) : State S B n W D C (m + 1) := by
  let F := family x hm r
  let p := (IntegralHistoryCriticalBits.source F).annihilator []
  let d := IntegralScalarRootHistoryBounds.degree F []
  exact {
    scalarPrefix := UniformIntegralPrefix.step x.scalarPrefix hm (Nat.two_pow_pos B) p d
    bank := x.bank.rootStep hm p d (IntegralClearedCriticalLeadingBits.integer (IntegralHistoryCriticalBits.source F) [])
    history := IntegralScalarRootHistoryBounds.History.step F [] x.bank x.history (r.select m)
      (fun _ => rfl) (fun _ => rfl) r.low_height r.leading_height le_rfl le_rfl r.degree_le (degree_le x hm r hN) }

noncomputable def run (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) : State S B n W D C rules.length :=
  match rules with
  | [] => base S B n W D C
  | r :: rs => step (run rs (by simp only [List.length_cons] at h; omega) hN)
      (by simp only [List.length_cons] at h; omega) r hN

theorem run_generators (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length) :
    (run rules h hN).bank.numerator i = (run rules h hN).scalarPrefix.basis.generator i :=
  (run rules h hN).history.generators i

theorem run_denominators_ne_zero (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length) :
    (run rules h hN).bank.denominator i ≠ 0 := (run rules h hN).history.denominators_ne_zero i

theorem run_bounds (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) :
    (run rules h hN).bank.Bounds
      (IntegralHistoryGlobalHeightBounds.height (n + 1) (count S B) W D (2 ^ B) C (S + 1)) :=
  (run rules h hN).history.uniform_bounds

def Command.instruction (r : Command n W D C) (m : ℕ) : IntegralCriticalDenominatorScript.Instruction where
  leading := r.leading
  degree := r.degree
  exponent := (PurePowerReductionBounds.bound (n - r.offset.val + 1) r.degree + 1) *
    PurePowerReductionBounds.dimension (n - r.offset.val + 1) r.degree
  indices := List.ofFn (fun i => if r.selected i < m then r.selected i else m)

theorem selectorIndex_select (r : Command n W D C) (m : ℕ) (i : Fin (n + 1)) :
    IntegralCriticalDenominatorScript.selectorIndex (r.select m i) = if r.selected i < m then r.selected i else m := by
  unfold Command.select IntegralCriticalDenominatorScript.selectorIndex
  split_ifs <;> rfl

theorem instruction_eq (x : State S B n W D C m) (hm : m ≤ S) (r : Command n W D C) :
    IntegralCriticalDenominatorScript.instruction (family x hm r) [] (r.select m) = r.instruction m := by
  change (⟨r.leading, r.degree,
    (PurePowerReductionBounds.bound (n - r.offset.val + 1) r.degree + 1) *
      PurePowerReductionBounds.dimension (n - r.offset.val + 1) r.degree,
    List.ofFn (fun i => IntegralCriticalDenominatorScript.selectorIndex (r.select m i))⟩ : IntegralCriticalDenominatorScript.Instruction) = _
  simp only [Command.instruction, selectorIndex_select]

theorem step_denominators (x : State S B n W D C m) (hm : m ≤ S) (r : Command n W D C)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) :
    List.ofFn (step x hm r hN).bank.denominator = (r.instruction m).next (List.ofFn x.bank.denominator) :: List.ofFn x.bank.denominator := by
  have H := IntegralCriticalDenominatorScript.instruction_next (family x hm r) [] x.bank (r.select m) (fun _ => rfl)
  rw [instruction_eq] at H
  change List.ofFn (Fin.cons
    (IntegralClearedCriticalLeadingBits.integer (IntegralHistoryCriticalBits.source (family x hm r)) []) x.bank.denominator) = _
  rw [List.ofFn_succ]
  exact congrArg (fun z => z :: List.ofFn x.bank.denominator) H.symm

/-- Commands are newest first; their residue instructions execute oldest first. -/
def instructions : List (Command n W D C) → List IntegralCriticalDenominatorScript.Instruction
  | [] => []
  | r :: rs => instructions rs ++ [r.instruction rs.length]

theorem instructions_length (rules : List (Command n W D C)) : (instructions rules).length = rules.length := by
  induction rules with
  | nil => rfl
  | cons r rs ih => simp only [instructions, List.length_append, List.length_cons, List.length_nil, ih]

theorem execute_instructions (rules : List (Command n W D C))
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) :
    ∀ h : rules.length ≤ S + 1,
      IntegralCriticalDenominatorScript.execute (instructions rules) = List.ofFn (run rules h hN).bank.denominator := by
  induction rules with
  | nil => intro h; rfl
  | cons r rs ih =>
    intro h
    have HT : rs.length ≤ S + 1 := by simp only [List.length_cons] at h; omega
    have HS : rs.length ≤ S := by simp only [List.length_cons] at h; omega
    change IntegralCriticalDenominatorScript.execute (instructions rs ++ [r.instruction rs.length]) =
      List.ofFn (step (run rs HT hN) HS r hN).bank.denominator
    rw [IntegralCriticalDenominatorScript.execute_append, ih HT]
    exact (step_denominators (run rs HT hN) HS r hN).symm

/-- The first `j` births are the oldest suffix of the command list. -/
def past (rules : List (Command n W D C)) (j : ℕ) : List (Command n W D C) :=
  rules.drop (rules.length - min j rules.length)

theorem past_length (rules : List (Command n W D C)) (j : ℕ) : (past rules j).length = min j rules.length := by
  have H := min_le_right j rules.length
  simp only [past, List.length_drop]
  omega

theorem past_all (rules : List (Command n W D C)) (j : ℕ) (h : rules.length ≤ j) : past rules j = rules := by
  simp only [past, min_eq_right h, Nat.sub_self, List.drop_zero]

theorem past_cons_of_le (r : Command n W D C) (rs : List (Command n W D C)) (j : ℕ) (h : j ≤ rs.length) :
    past (r :: rs) j = past rs j := by
  have H : j ≤ rs.length + 1 := by omega
  simp only [past, List.length_cons, min_eq_left H, min_eq_left h]
  have HE : rs.length + 1 - j = (rs.length - j) + 1 := by omega
  rw [HE, List.drop_succ_cons]

theorem instructions_past (rules : List (Command n W D C)) (j : ℕ) :
    instructions (past rules j) = (instructions rules).take j := by
  induction rules with
  | nil => simp only [past, List.drop_nil, instructions, List.take_nil]
  | cons r rs ih =>
    by_cases h : j ≤ rs.length
    · rw [past_cons_of_le r rs j h, ih, instructions, List.take_append_of_le_length]
      simpa only [instructions_length] using h
    · have H : (r :: rs).length ≤ j := by simp only [List.length_cons]; omega
      rw [past_all (r :: rs) j H, List.take_of_length_le (by simpa only [instructions_length] using H)]

noncomputable def stateAt (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (j : ℕ) : State S B n W D C (past rules j).length :=
  run (past rules j) ((by rw [past_length]; exact (min_le_right j rules.length).trans h)) hN

theorem execute_take (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (j : ℕ) :
    IntegralCriticalDenominatorScript.execute ((instructions rules).take j) = List.ofFn (stateAt rules h hN j).bank.denominator := by
  rw [← instructions_past]
  exact execute_instructions (past rules j) hN _

/-- Native instruction access computes actual bank residues without an algebraic reader. -/
theorem bank_denominator_reader_FP (S B n W D C : List Bool → ℕ)
    (rules : ∀ c, List (Command (n c) (W c) (D c) (C c)))
    (hlen : ∀ c, (rules c).length ≤ S c + 1)
    (hwidth : ∀ c, PurePowerReductionBounds.dimension (n c + 1) (D c) ≤ 2 ^ B c)
    (modulus : List Bool → ℕ) (hm : ∀ c, modulus c ≠ 0)
    (a : IntegralDenominatorPass.Access
      (IntegralCriticalDenominatorScript.program (fun c => instructions (rules c)) modulus hm))
    (j : List Bool → ℕ) (hj : BinaryFn j) :
    (fun c => MatrixPower.residueBits
      (((List.ofFn (run (rules c) (hlen c) (hwidth c)).bank.denominator)[j c]?).getD 0 : ZMod (modulus c))) ∈ FP := by
  have H := IntegralCriticalDenominatorScript.script_reader_FP (fun c => instructions (rules c)) modulus hm a j hj
  refine mem_FP_of_eq H (fun c => ?_)
  rw [execute_instructions (rules c) (hwidth c) (hlen c)]

theorem bank_prefix_denominator_reader_FP (S B n W D C : List Bool → ℕ)
    (rules : ∀ c, List (Command (n c) (W c) (D c) (C c)))
    (hlen : ∀ c, (rules c).length ≤ S c + 1)
    (hwidth : ∀ c, PurePowerReductionBounds.dimension (n c + 1) (D c) ≤ 2 ^ B c)
    (modulus : List Bool → ℕ) (hm : ∀ c, modulus c ≠ 0)
    (a : IntegralDenominatorPass.Access
      (IntegralCriticalDenominatorScript.program (fun c => instructions (rules c)) modulus hm))
    (length : List Bool → ℕ) (hl : BinaryFn length) (j : List Bool → ℕ) (hj : BinaryFn j) :
    (fun c => MatrixPower.residueBits
      (((List.ofFn (stateAt (rules c) (hlen c) (hwidth c) (length c)).bank.denominator)[j c]?).getD 0 : ZMod (modulus c))) ∈ FP := by
  have H := IntegralDenominatorPass.prefix_reader_FP
    (IntegralCriticalDenominatorScript.program (fun c => instructions (rules c)) modulus hm) a length hl j hj
  refine mem_FP_of_eq H (fun c => ?_)
  change MatrixPower.residueBits
    (((IntegralDenominatorPass.integers (IntegralCriticalDenominatorScript.program (fun c => instructions (rules c)) modulus hm)
      c (min (length c) (instructions (rules c)).length))[j c]?).getD 0 : ZMod (modulus c)) = _
  rw [IntegralCriticalDenominatorScript.program_integers (fun c => instructions (rules c)) modulus hm c _ (min_le_right _ _)]
  have HT : (instructions (rules c)).take (min (length c) (instructions (rules c)).length) =
      (instructions (rules c)).take (length c) := by
    by_cases h : length c ≤ (instructions (rules c)).length
    · rw [min_eq_left h]
    · have HN : (instructions (rules c)).length ≤ length c := by omega
      rw [min_eq_right HN, List.take_length, List.take_of_length_le HN]
  rw [HT, execute_take (rules c) (hlen c) (hwidth c) (length c)]

end LeanCanny.Algebra.IntegralCriticalScript
