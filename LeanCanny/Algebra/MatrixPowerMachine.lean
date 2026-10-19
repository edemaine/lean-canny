/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerEntry
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Function.Iterate

/-!
# A continuation machine for streamed matrix powering

The machine evaluates the two factors of each summand sequentially. A frame
retains the parent query, one summation index, an accumulator, and at most one
returned scalar. It stores neither a matrix power nor a list of summands.

The transition count treats scalar arithmetic and input-entry access as single
operations. This is an abstract machine: bit encodings and certified costs of
those operations are still required for a Turing-machine space theorem.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower

structure Query (n : ℕ) where
  height : ℕ
  exponent : ℕ
  row : Fin n
  col : Fin n

namespace Query
variable {n : ℕ}

def left (q : Query n) (k : Fin n) : Query n :=
  ⟨q.height - 1, q.exponent / 2, q.row, k⟩

def right (q : Query n) (k : Fin n) : Query n :=
  ⟨q.height - 1, q.exponent - q.exponent / 2, k, q.col⟩

def last (q : Query n) : Fin n := ⟨n - 1, by have := q.row.isLt; omega⟩

def value {R : Type*} [Semiring R] (A : Matrix (Fin n) (Fin n) R) (q : Query n) : R :=
  entry A q.height q.exponent q.row q.col

def work (q : Query n) : ℕ := MatrixPower.work n q.height q.exponent

end Query

inductive Frame (R : Type*) (n : ℕ) where
  | left (parent : Query n) (index : Fin n) (acc : R)
  | right (parent : Query n) (index : Fin n) (acc leftValue : R)

inductive State (R : Type*) (n : ℕ) where
  | eval (query : Query n) (stack : List (Frame R n))
  | ret (value : R) (stack : List (Frame R n))
  | done (value : R)

variable {R : Type*} [Semiring R] {n : ℕ}

def step (A : Matrix (Fin n) (Fin n) R) : State R n → State R n
  | .eval q stack =>
      if q.exponent = 0 then .ret (if q.row = q.col then 1 else 0) stack
      else if q.exponent = 1 then .ret (A q.row q.col) stack
      else if q.height = 0 then .ret 0 stack
      else .eval (q.left q.last) (.left q q.last 0 :: stack)
  | .ret x [] => .done x
  | .ret x (.left q k acc :: stack) =>
      .eval (q.right k) (.right q k acc x :: stack)
  | .ret x (.right q k acc lhs :: stack) =>
      if k.val = 0 then .ret (acc + lhs * x) stack
      else
        let next : Fin n := ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
        .eval (q.left next) (.left q next (acc + lhs * x) :: stack)
  | .done x => .done x

def term (A : Matrix (Fin n) (Fin n) R) (q : Query n) (k : Fin n) : R :=
  (q.left k).value A * (q.right k).value A

/-- Semantic sum only; it is not part of the machine's stored state. -/
def sumBelow (A : Matrix (Fin n) (Fin n) R) (q : Query n) (k : ℕ) : R :=
  ∑ l ∈ Finset.range k, if hl : l < n then term A q ⟨l, hl⟩ else 0

@[simp] theorem prefix_zero (A : Matrix (Fin n) (Fin n) R) (q : Query n) :
    sumBelow A q 0 = 0 := by simp [sumBelow]

theorem prefix_succ (A : Matrix (Fin n) (Fin n) R) (q : Query n) (k : Fin n) :
    sumBelow A q (k.val + 1) = sumBelow A q k.val + term A q k := by
  simp only [sumBelow, Finset.sum_range_succ, dite_eq_left k.isLt]

theorem prefix_full (A : Matrix (Fin n) (Fin n) R) (q : Query n) :
    sumBelow A q n = ∑ k, term A q k := by
  rw [sumBelow, ← Fin.sum_univ_eq_sum_range]
  simp only [Fin.isLt, ↓reduceDIte]

theorem value_expand (A : Matrix (Fin n) (Fin n) R) (q : Query n)
    (hh : 0 < q.height) (he : 1 < q.exponent) : q.value A = sumBelow A q n := by
  rw [prefix_full]
  rcases q with ⟨h, e, i, j⟩
  change 0 < h at hh
  change 1 < e at he
  cases h with
  | zero => omega
  | succ h =>
      have he0 : e ≠ 0 := by omega
      have he1 : e ≠ 1 := by omega
      simp only [Query.value, entry, he0, he1, ↓reduceIte, term, Query.left, Query.right,
        Nat.add_sub_cancel]

def Frame.plug (A : Matrix (Fin n) (Fin n) R) : Frame R n → R → R
  | .left q k acc, x => acc + x * (q.right k).value A + sumBelow A q k.val
  | .right q k acc lhs, x => acc + lhs * x + sumBelow A q k.val

def stackValue (A : Matrix (Fin n) (Fin n) R) : List (Frame R n) → R → R
  | [], x => x
  | f :: stack, x => stackValue A stack (f.plug A x)

def value (A : Matrix (Fin n) (Fin n) R) : State R n → R
  | .eval q stack => stackValue A stack (q.value A)
  | .ret x stack => stackValue A stack x
  | .done x => x

theorem step_value (A : Matrix (Fin n) (Fin n) R) (s : State R n) :
    value A (step A s) = value A s := by
  cases s with
  | eval q stack =>
      by_cases he0 : q.exponent = 0
      · cases hq : q.height <;> simp [step, he0, value, Query.value, hq, entry]
      by_cases he1 : q.exponent = 1
      · cases hq : q.height <;> simp [step, he1, value, Query.value, hq, entry]
      by_cases hh : q.height = 0
      · simp [step, he0, he1, hh, value, Query.value, entry]
      · simp only [step, he0, he1, hh, ↓reduceIte, value, stackValue, Frame.plug,
          zero_add, value_expand A q (by omega) (by omega)]
        have hlast : n = q.last.val + 1 := by
          have := q.row.isLt
          simp only [Query.last]
          omega
        have hp := prefix_succ A q q.last
        rw [← hlast] at hp
        rw [hp]
        simp only [term]
        congr 1
        exact add_comm _ _
  | ret x stack =>
      cases stack with
      | nil => rfl
      | cons f stack =>
          cases f with
          | left q k acc => rfl
          | right q k acc lhs =>
              cases hk : k.val with
              | zero => simp [step, hk, value, stackValue, Frame.plug]
              | succ l =>
                  simp only [step, hk, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
                    ↓reduceIte, Nat.add_sub_cancel, value, stackValue, Frame.plug]
                  have hnext : l < n := by have := k.isLt; omega
                  have hp := prefix_succ A q (⟨l, hnext⟩ : Fin n)
                  rw [hp]
                  simp only [term]
                  congr 1
                  ac_rfl
  | done x => rfl

end LeanCanny.Algebra.MatrixPower
