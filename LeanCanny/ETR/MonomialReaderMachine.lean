/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.IndexedExpansionBounds

/-!
# A stack controller for one indexed monomial

Addition follows one summand. Multiplication divides the index by the right
child's monomial count and schedules both children. Leaf values accumulate in
a monoid, giving coefficients by multiplication and selected-variable exponents
by addition. The number of transitions is bounded by the original term size.
-/

@[expose] public section

namespace LeanCanny.ETR.MonomialReader

structure Task where
  term : Term
  index : ℕ
  deriving DecidableEq, Repr

structure State (R : Type*) where
  todo : List Task
  value : R

variable {R : Type*} [Monoid R]

def fold (constant : ℤ → R) (variableValue : ℕ → R) : Term → ℕ → R
  | .const z, _ => constant z
  | .var i, _ => variableValue i
  | .add a b, r => if r < a.monomialCount then fold constant variableValue a r
    else fold constant variableValue b (r - a.monomialCount)
  | .mul a b, r => fold constant variableValue a (r / b.monomialCount) *
    fold constant variableValue b (r % b.monomialCount)

def step (constant : ℤ → R) (variableValue : ℕ → R) (s : State R) : State R :=
  match s.todo with
  | [] => s
  | ⟨.const z, _⟩ :: rest => ⟨rest, s.value * constant z⟩
  | ⟨.var i, _⟩ :: rest => ⟨rest, s.value * variableValue i⟩
  | ⟨.add a b, r⟩ :: rest =>
    if r < a.monomialCount then ⟨⟨a, r⟩ :: rest, s.value⟩
    else ⟨⟨b, r - a.monomialCount⟩ :: rest, s.value⟩
  | ⟨.mul a b, r⟩ :: rest =>
    ⟨⟨a, r / b.monomialCount⟩ :: ⟨b, r % b.monomialCount⟩ :: rest, s.value⟩

def work : Term → ℕ → ℕ
  | .const _, _ | .var _, _ => 1
  | .add a b, r => 1 + if r < a.monomialCount then work a r else work b (r - a.monomialCount)
  | .mul a b, r => 1 + work a (r / b.monomialCount) + work b (r % b.monomialCount)

theorem work_le_dataSize (t : Term) (r : ℕ) : work t r ≤ t.toData.size := by
  induction t generalizing r with
  | const z => exact LeanCanny.Data.size_pos
  | var i => simp [work]
  | add a b ha hb =>
    simp only [work, Term.dataSize_add]
    split_ifs <;> have := ha r <;> have := hb (r - a.monomialCount) <;> omega
  | mul a b ha hb =>
    have hA := ha (r / b.monomialCount)
    have hB := hb (r % b.monomialCount)
    simp only [work, Term.dataSize_mul]
    omega

theorem visit_steps (constant : ℤ → R) (variableValue : ℕ → R) (t : Term) (r : ℕ)
    (todo : List Task) (v : R) :
    (step constant variableValue)^[work t r] ⟨⟨t, r⟩ :: todo, v⟩ =
      ⟨todo, v * fold constant variableValue t r⟩ := by
  induction t generalizing r todo v with
  | const z | var z => rfl
  | add a b ha hb =>
    by_cases hr : r < a.monomialCount
    · rw [work, ite_eq_left hr, Nat.add_comm 1, Function.iterate_succ_apply]
      change (step constant variableValue)^[work a r] (if r < a.monomialCount then _ else _) = _
      rw [ite_eq_left hr, ha]
      simp only [fold, hr, ↓reduceIte]
    · rw [work, ite_eq_right hr, Nat.add_comm 1, Function.iterate_succ_apply]
      change (step constant variableValue)^[work b (r - a.monomialCount)] (if r < a.monomialCount then _ else _) = _
      rw [ite_eq_right hr, hb]
      simp only [fold, hr, ↓reduceIte]
  | mul a b ha hb =>
    rw [work, show 1 + work a (r / b.monomialCount) + work b (r % b.monomialCount) =
      (work b (r % b.monomialCount) + work a (r / b.monomialCount)) + 1 by omega, Function.iterate_succ_apply]
    change (step constant variableValue)^[work b (r % b.monomialCount) + work a (r / b.monomialCount)]
      ⟨⟨a, r / b.monomialCount⟩ :: ⟨b, r % b.monomialCount⟩ :: todo, v⟩ = _
    rw [Function.iterate_add_apply, ha, hb]
    simp only [fold, mul_assoc]

theorem run_steps (constant : ℤ → R) (variableValue : ℕ → R) (t : Term) (r fuel : ℕ)
    (hfuel : work t r ≤ fuel) :
    (step constant variableValue)^[fuel] ⟨[⟨t, r⟩], 1⟩ = ⟨[], fold constant variableValue t r⟩ := by
  obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le hfuel
  rw [he, Nat.add_comm (work t r), Function.iterate_add_apply, visit_steps, one_mul]
  exact Function.iterate_fixed (by rfl) extra

theorem fold_coefficient (t : Term) (r : ℕ) : fold (R := ℤ) id (fun _ => 1) t r = t.monomialCoefficient r := by
  induction t generalizing r <;> simp_all [fold, Term.monomialCoefficient, apply_ite]

theorem fold_coefficient_cast {S : Type*} [Monoid S] (φ : ℤ →* S) (t : Term) (r : ℕ) :
    fold φ (fun _ => 1) t r = φ (t.monomialCoefficient r) := by
  induction t generalizing r <;> simp_all [fold, Term.monomialCoefficient, apply_ite]

theorem fold_exponent (t : Term) (r i : ℕ) :
    (fold (R := Multiplicative ℕ) (fun _ => Multiplicative.ofAdd 0)
      (fun j => Multiplicative.ofAdd (if i = j then 1 else 0)) t r).toAdd = t.monomialExponent r i := by
  induction t generalizing r <;> simp_all [fold, Term.monomialExponent, apply_ite]

def pendingSize (todo : List Task) : ℕ := (todo.map (fun q => q.term.toData.size)).sum

theorem pendingSize_step_le (constant : ℤ → R) (variableValue : ℕ → R) (s : State R) :
    pendingSize (step constant variableValue s).todo ≤ pendingSize s.todo := by
  rcases s with ⟨todo, v⟩
  cases todo with
  | nil => exact le_rfl
  | cons q rest =>
    rcases q with ⟨t, r⟩
    cases t <;> simp only [step, pendingSize, List.map_cons, List.sum_cons]
    · omega
    · omega
    · split_ifs <;> simp only [List.map_cons, List.sum_cons, Term.dataSize_add] <;> omega
    · simp only [Term.dataSize_mul]; omega

theorem index_le_step (constant : ℤ → R) (variableValue : ℕ → R) (s : State R) (I : ℕ)
    (hi : ∀ q ∈ s.todo, q.index ≤ I) : ∀ q ∈ (step constant variableValue s).todo, q.index ≤ I := by
  rcases s with ⟨todo, v⟩
  cases todo with
  | nil => simpa only [step] using hi
  | cons q rest =>
    rcases q with ⟨t, r⟩
    have hr : r ≤ I := hi _ (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, q.index ≤ I := fun q hq => hi q (List.mem_cons_of_mem _ hq)
    cases t <;> simp only [step]
    · exact hrest
    · exact hrest
    · split_ifs <;> simp only [List.forall_mem_cons]
      · exact ⟨hr, hrest⟩
      · exact ⟨(Nat.sub_le r _).trans hr, hrest⟩
    · simp only [List.forall_mem_cons]
      exact ⟨(Nat.div_le_self _ _).trans hr, (Nat.mod_le _ _).trans hr, hrest⟩

end LeanCanny.ETR.MonomialReader
