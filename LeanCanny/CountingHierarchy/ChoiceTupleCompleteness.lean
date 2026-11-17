/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ChoiceTupleEncoding
public import Mathlib.Tactic.FinCases

/-! # Every bounded collection of final discrete choices has a short word -/

public section

namespace LeanCanny.CountingHierarchy

open scoped Classical

theorem exists_choiceTupleWord {n : ℕ} (N H D : ℕ) (k : Fin (N + 1))
    (j : Fin n → ℕ) (L : Fin n → FingerprintLabelData)
    (hj : ∀ i, j i ≤ H) (hL : ∀ i, (L i).Bounded D) :
    ∃ word : List Bool, word.length = choiceTupleWidth N H D n ∧ choiceDegree N word = k ∧
      (∀ i, choiceIndex H word i.val = j i) ∧ ∀ i, choiceLabel D word i.val = L i := by
  choose r g t hr hg ht heq using fun i => exists_normalizedFingerprintData D (L i) (hL i)
  let data : Fin n → Fin 4 → ℕ := fun i =>
    Fin.cases (j i) (Fin.cases (r i) (Fin.cases (g i) (Fin.cases (t i) Fin.elim0)))
  let M := choiceTupleBound N H D
  have hN : N ≤ M := by dsimp only [M, choiceTupleBound]; omega
  have hH : H ≤ M := by dsimp only [M, choiceTupleBound]; omega
  have hmu : 2 * (D ^ 3 + 2) ≤ M := by dsimp only [M, choiceTupleBound]; omega
  have htarget : 2 * (D * (2 * (D ^ 3 + 2))) + 1 ≤ M := by dsimp only [M, choiceTupleBound]; omega
  have hd (i : Fin n) (s : Fin 4) : data i s ≤ M := by
    fin_cases s
    · exact (hj i).trans hH
    · exact (hr i).trans hmu
    · exact (hg i).trans hmu
    · exact (ht i).trans htarget
  obtain ⟨word, hlen, hword⟩ := exists_natTupleWord M (1 + 4 * n) (choiceTupleData k.val data)
    (choiceTupleData_length k.val data).le (choiceTupleData_mem_bound M k.val data
      ((Nat.le_of_lt_succ k.isLt).trans hN) hd)
  refine ⟨word, hlen, ?_, ?_, ?_⟩
  · apply Fin.ext
    change (natTupleWord word)[0]?.getD 0 % (N + 1) = k.val
    rw [hword]
    simp only [choiceTupleData, List.getElem?_cons_zero, Option.getD_some, Nat.mod_eq_of_lt k.isLt]
  · intro i
    unfold choiceIndex choiceEntry
    rw [hword]
    have hget := choiceTupleData_get k.val data i (0 : Fin 4)
    have hv : (0 : Fin 4).val = 0 := by decide
    simp only [hv] at hget
    rw [hget]
    change j i % (H + 1) = j i
    exact Nat.mod_eq_of_lt (by have := hj i; omega)
  · intro i
    unfold choiceLabel choiceEntry
    rw [hword]
    have hget1 := choiceTupleData_get k.val data i (1 : Fin 4)
    have hget2 := choiceTupleData_get k.val data i (2 : Fin 4)
    have hget3 := choiceTupleData_get k.val data i (3 : Fin 4)
    simp only [show (1 : Fin 4).val = 1 by decide] at hget1
    simp only [show (2 : Fin 4).val = 2 by decide] at hget2
    simp only [show (3 : Fin 4).val = 3 by decide] at hget3
    rw [hget1, hget2, hget3]
    exact heq i

end LeanCanny.CountingHierarchy
