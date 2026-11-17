/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.NatTupleWitnessEncoding
public import LeanCanny.CountingHierarchy.NormalizedFingerprintData

/-! # Polynomial-width encoding of one degree choice and four entries per coordinate -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped Classical

def choiceTupleBound (N H D : ℕ) : ℕ :=
  max N (max H (max (2 * (D ^ 3 + 2)) (2 * (D * (2 * (D ^ 3 + 2))) + 1)))

def choiceTupleWidth (N H D n : ℕ) : ℕ := natTupleWitnessWidth (choiceTupleBound N H D) (1 + 4 * n)

def choiceDegree (N : ℕ) (word : List Bool) : Fin (N + 1) :=
  ⟨(natTupleWord word)[0]?.getD 0 % (N + 1), Nat.mod_lt _ (by omega)⟩

def choiceEntry (word : List Bool) (i j : ℕ) : ℕ := (natTupleWord word)[1 + 4 * i + j]?.getD 0

def choiceIndex (H : ℕ) (word : List Bool) (i : ℕ) : ℕ := choiceEntry word i 0 % (H + 1)

def choiceLabel (D : ℕ) (word : List Bool) (i : ℕ) : FingerprintLabelData :=
  normalizedFingerprintData D (choiceEntry word i 1) (choiceEntry word i 2) (choiceEntry word i 3)

theorem choiceIndex_le (H : ℕ) (word : List Bool) (i : ℕ) : choiceIndex H word i ≤ H :=
  Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.zero_lt_succ _))

theorem choiceLabel_bounded (D : ℕ) (word : List Bool) (i : ℕ) : (choiceLabel D word i).Bounded D :=
  normalizedFingerprintData_bounded _ _ _ _

def choiceTupleData {n : ℕ} (k : ℕ) (data : Fin n → Fin 4 → ℕ) : List ℕ :=
  k :: List.ofFn (fun h : Fin (4 * n) => data ⟨h.val / 4, by omega⟩ ⟨h.val % 4, Nat.mod_lt _ (by decide)⟩)

theorem choiceTupleData_length {n : ℕ} (k : ℕ) (data : Fin n → Fin 4 → ℕ) :
    (choiceTupleData k data).length = 1 + 4 * n := by simp [choiceTupleData, Nat.add_comm]

theorem choiceTupleData_get {n : ℕ} (k : ℕ) (data : Fin n → Fin 4 → ℕ) (i : Fin n) (j : Fin 4) :
    (choiceTupleData k data)[1 + 4 * i.val + j.val]?.getD 0 = data i j := by
  have hlt : 4 * i.val + j.val < 4 * n := by have := i.isLt; have := j.isLt; omega
  have hdiv : (4 * i.val + j.val) / 4 = i.val := by have := j.isLt; omega
  have hmod : (4 * i.val + j.val) % 4 = j.val := by have := j.isLt; omega
  simp only [choiceTupleData, show 1 + 4 * i.val + j.val = (4 * i.val + j.val) + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_ofFn, hlt, dite_true, Option.getD_some]
  congr 1 <;> apply Fin.ext <;> assumption

theorem choiceTupleData_mem_bound {n : ℕ} (M k : ℕ) (data : Fin n → Fin 4 → ℕ)
    (hk : k ≤ M) (hd : ∀ i j, data i j ≤ M) : ∀ t ∈ choiceTupleData k data, t ≤ M := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact hk
  · obtain ⟨h, rfl⟩ := List.mem_ofFn.mp ht
    exact hd _ _

end LeanCanny.CountingHierarchy
