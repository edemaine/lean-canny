/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationCompilerMachine

/-!
# Bounds throughout the equation compiler's stack run

The pending program has a decreasing syntactic budget. Each step adds at most
one value and one equation. The counter agrees with the top value and bounds
all older values, so it increases by at most one per step. These invariants
also bound all intermediate masked polynomial expressions.
-/

@[expose] public section

namespace LeanCanny.ETR.EquationCompiler

def programBudget : List Instruction → ℕ
  | [] => 0
  | .visit p :: rest => p.budget + programBudget rest
  | .join _ :: rest => 1 + programBudget rest

def equationCount : List EquationSystem → ℕ
  | [] => 0
  | a :: rest => a.terms.length + equationCount rest

def valueSize : List EquationSystem → ℕ
  | [] => 0
  | a :: rest => a.dataSize + valueSize rest

def State.CounterOk (s : State) : Prop :=
  (∀ a ∈ s.values, a.next ≤ s.next) ∧
    (∀ a rest, s.values = a :: rest → a.next = s.next)

private theorem counterOk_push (todo : List Instruction) (values : List EquationSystem)
    (out : EquationSystem) (next : ℕ) (hvalues : ∀ a ∈ values, a.next ≤ next)
    (hle : next ≤ out.next) : State.CounterOk ⟨todo, out :: values, out.next⟩ := by
  constructor
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_rfl
    · exact (hvalues a ha).trans hle
  · intro a rest he
    have hh := (List.cons.inj he).1
    subst a
    rfl

theorem step_counter (s : State) (h : s.CounterOk) :
    s.next ≤ (step s).next ∧ (step s).next ≤ s.next + 1 ∧ (step s).CounterOk := by
  rcases s with ⟨todo, values, next⟩
  cases todo with
  | nil => exact ⟨le_rfl, by simp [step], h⟩
  | cons instruction todo =>
      cases instruction with
      | visit p =>
          cases p with
          | and p q | or p q => exact ⟨le_rfl, by simp [step], h⟩
          | truth | falsum | eqZero t | neZero t | ltZero t | nonneg t =>
              refine ⟨?_, ?_, counterOk_push todo values _ next h.1 ?_⟩ <;>
                simp [step, SignedFormula.equations]
      | join disjoin =>
          cases values with
          | nil => exact ⟨le_rfl, by simp [step], h⟩
          | cons b values =>
              cases values with
              | nil => exact ⟨le_rfl, by simp [step], h⟩
              | cons a values =>
                  have hb : b.next = next := h.2 b (a :: values) rfl
                  have hv : ∀ v ∈ values, v.next ≤ next := by
                    intro v hv
                    exact h.1 v (List.mem_cons_of_mem b (List.mem_cons_of_mem a hv))
                  cases disjoin
                  · refine ⟨?_, ?_, counterOk_push todo values (a.conjunction b) next hv ?_⟩ <;>
                      simp [step, EquationSystem.conjunction, hb]
                  · refine ⟨?_, ?_, counterOk_push todo values (a.disjunction b) next hv ?_⟩ <;>
                      simp [step, EquationSystem.disjunction, hb]

theorem step_programBudget_le (s : State) : programBudget (step s).todo ≤ programBudget s.todo := by
  rcases s with ⟨todo, values, next⟩
  cases todo with
  | nil => exact le_rfl
  | cons instruction todo =>
      cases instruction with
      | visit p =>
          cases p <;> simp [step, programBudget, SignedFormula.budget] <;> omega
      | join disjoin =>
          cases values with
          | nil => exact le_rfl
          | cons b values =>
              cases values with
              | nil => exact le_rfl
              | cons a values => simp [step, programBudget]

theorem step_valueCount_le (s : State) : (step s).values.length ≤ s.values.length + 1 := by
  rcases s with ⟨todo, values, next⟩
  cases todo with
  | nil => simp [step]
  | cons instruction todo =>
      cases instruction with
      | visit p => cases p <;> simp [step]
      | join disjoin =>
          cases values with
          | nil => simp [step]
          | cons b values =>
              cases values with
              | nil => simp [step]
              | cons a values => simp [step]

theorem step_equationCount_le (s : State) : equationCount (step s).values ≤ equationCount s.values + 1 := by
  rcases s with ⟨todo, values, next⟩
  cases todo with
  | nil => simp [step]
  | cons instruction todo =>
      cases instruction with
      | visit p => cases p <;> simp [step, equationCount, SignedFormula.equations, Nat.add_comm]
      | join disjoin =>
          cases values with
          | nil => simp [step]
          | cons b values =>
              cases values with
              | nil => simp [step]
              | cons a values =>
                  cases disjoin <;>
                    simp [step, equationCount, EquationSystem.conjunction, EquationSystem.disjunction,
                      List.length_append, List.length_map] <;> omega

def run (p : SignedFormula) (start fuel : ℕ) : State :=
  step^[fuel] ⟨[.visit p], [], start⟩

@[simp] theorem run_zero (p : SignedFormula) (start : ℕ) :
    run p start 0 = ⟨[.visit p], [], start⟩ := rfl

theorem run_succ (p : SignedFormula) (start fuel : ℕ) :
    run p start (fuel + 1) = step (run p start fuel) := Function.iterate_succ_apply' ..

theorem run_counterOk (p : SignedFormula) (start fuel : ℕ) : (run p start fuel).CounterOk := by
  induction fuel with
  | zero => simp [State.CounterOk]
  | succ fuel ih => rw [run_succ]; exact (step_counter _ ih).2.2

theorem run_programBudget_le (p : SignedFormula) (start fuel : ℕ) :
    programBudget (run p start fuel).todo ≤ p.budget := by
  induction fuel with
  | zero => simp [programBudget]
  | succ fuel ih => rw [run_succ]; exact (step_programBudget_le _).trans ih

theorem run_valueCount_le (p : SignedFormula) (start fuel : ℕ) : (run p start fuel).values.length ≤ fuel := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [run_succ]
      exact (step_valueCount_le _).trans (Nat.add_le_add_right ih 1)

theorem run_equationCount_le (p : SignedFormula) (start fuel : ℕ) :
    equationCount (run p start fuel).values ≤ fuel := by
  induction fuel with
  | zero => simp [equationCount]
  | succ fuel ih =>
      rw [run_succ]
      exact (step_equationCount_le _).trans (Nat.add_le_add_right ih 1)

theorem run_next_le (p : SignedFormula) (start fuel : ℕ) : (run p start fuel).next ≤ start + fuel := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [run_succ]
      have hs := (step_counter _ (run_counterOk p start fuel)).2.1
      omega

theorem step_valueSize_le (s : State) (h : s.CounterOk) :
    valueSize (step s).values ≤ valueSize s.values + programBudget s.todo + 4 * s.next + 58 +
      equationCount s.values * (2 * s.next + 62) := by
  rcases s with ⟨todo, values, next⟩
  cases todo with
  | nil => simp only [step]; omega
  | cons instruction todo =>
      cases instruction with
      | visit p =>
          cases p with
          | and p q | or p q => simp only [step]; omega
          | truth | falsum | eqZero t | neZero t | ltZero t | nonneg t =>
              simp only [step, SignedFormula.equations, valueSize, EquationSystem.dataSize,
                Term.listDataSize_nil, Term.listDataSize_cons, Term.dataSize_const_one,
                Term.dataSize_nonzeroEquation, Term.dataSize_negativeEquation,
                Term.dataSize_nonnegativeEquation, programBudget, SignedFormula.budget]
              omega
      | join disjoin =>
          cases values with
          | nil => simp only [step]; omega
          | cons b values =>
              cases values with
              | nil => simp only [step]; omega
              | cons a values =>
                  cases disjoin
                  · simp only [step, Bool.false_eq_true, ite_false, valueSize,
                      EquationSystem.dataSize_conjunction]
                    omega
                  · have hb : b.next ≤ next := h.1 b (List.mem_cons_self ..)
                    have haCost := Nat.mul_le_mul_left a.terms.length
                      (show 2 * b.next + 18 ≤ 2 * next + 62 by omega)
                    have hbCost := Nat.mul_le_mul_left b.terms.length
                      (show 2 * b.next + 62 ≤ 2 * next + 62 by omega)
                    simp only [step, ite_true, valueSize, EquationSystem.dataSize_disjunction,
                      equationCount, Nat.add_mul]
                    omega

def growthCap (budget start fuel : ℕ) : ℕ :=
  budget + 4 * (start + fuel) + 58 + fuel * (2 * (start + fuel) + 62)

/-- All previously produced polynomials remain bounded throughout the run. -/
theorem run_valueSize_le (p : SignedFormula) (start fuel k : ℕ) (hk : k ≤ fuel) :
    valueSize (run p start k).values ≤ k * growthCap p.budget start fuel := by
  revert hk
  induction k with
  | zero => intro _; simp [valueSize]
  | succ k ih =>
      intro hk
      have hk' : k ≤ fuel := by omega
      have hp := ih hk'
      have hs := step_valueSize_le _ (run_counterOk p start k)
      have hb := run_programBudget_le p start k
      have hn := run_next_le p start k
      have hc := run_equationCount_le p start k
      have hm := Nat.mul_le_mul (hc.trans hk')
        (show 2 * (run p start k).next + 62 ≤ 2 * (start + fuel) + 62 by omega)
      rw [run_succ]
      simp only [Nat.add_mul, Nat.one_mul]
      dsimp only [growthCap] at *
      omega

/-- A concrete cubic bound for every intermediate equation list of a formula run.
The initial counter is the input bit length, reserving all original variables. -/
theorem formula_run_valueSize_le (p : Formula) (fuel : ℕ) (hfuel : fuel ≤ 2 * p.encode.length) :
    valueSize (run (p.toSigned true) p.encode.length fuel).values ≤ 1000 * (p.encode.length + 1) ^ 3 := by
  let n := p.encode.length
  have hb : (p.toSigned true).budget ≤ n := by
    simpa only [n, Formula.encode, Complexity.Data.length_toBits] using p.toSigned_budget_le true
  have hs := run_valueSize_le (p.toSigned true) n (2 * n) fuel hfuel
  have hg : growthCap (p.toSigned true).budget n (2 * n) ≤ 200 * (n + 1) ^ 2 := by
    dsimp only [growthCap]
    nlinarith
  have hm := Nat.mul_le_mul hfuel hg
  apply hs.trans
  apply hm.trans
  change 2 * n * (200 * (n + 1) ^ 2) ≤ 1000 * (n + 1) ^ 3
  calc
    _ = 400 * n * (n + 1) ^ 2 := by ring
    _ ≤ 1000 * (n + 1) * (n + 1) ^ 2 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

end LeanCanny.ETR.EquationCompiler
