/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedAnnihilatorPreparation

/-! # Every subtree of a completely prepared table is consistent -/

@[expose] public section

namespace LeanCanny.Algebra.BalancedTablePolynomials
open LeanCanny.Encoding
open SeparableBits (Family)

theorem Consistent.subtree (B : Family) (f : List Bool) (leaves : ℕ → SeparableIntegerPolynomial)
    (N : ℕ) (hc : Consistent B f leaves N 0) (h i : ℕ) (hh : h ≤ N) (hi : i < 2 ^ (N - h)) :
    Consistent B f leaves h i := by
  have hall : ∀ d, d ≤ N → ∀ j, j < 2 ^ d → Consistent B f leaves (N - d) j := by
    intro d
    induction d with
    | zero =>
      intro _ j hj
      have hj' : j = 0 := by simpa only [pow_zero] using Nat.eq_zero_of_le_zero (by omega : j ≤ 0)
      simpa only [Nat.sub_zero, hj'] using hc
    | succ d ih =>
      intro hd j hj
      have hp : j / 2 < 2 ^ d := by rw [pow_succ] at hj; omega
      have H := ih (by omega) (j / 2) hp
      have he : N - d = (N - (d + 1)) + 1 := by omega
      rw [he] at H
      obtain ⟨hl, hr, _, _, _⟩ := H
      have hm := Nat.mod_lt j (by decide : 0 < 2)
      have hjd := Nat.mod_add_div j 2
      by_cases hz : j % 2 = 0
      · have he' : j = 2 * (j / 2) := by omega
        rw [he']
        exact hl
      · have he' : j = 2 * (j / 2) + 1 := by omega
        rw [he']
        exact hr
  have H := hall (N - h) (by omega) i hi
  simpa only [Nat.sub_sub_self hh] using H

end LeanCanny.Algebra.BalancedTablePolynomials

namespace LeanCanny.Algebra.PaddedAnnihilatorPreparation
open LeanCanny.Encoding
open SeparableBits (Family)
open PaddedAnnihilatorBits BalancedDirectionPreparation

theorem prepare_ready (B : Family) (count D b : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (hheight : ∀ c i, i < count c → B.height (pair c (BinaryNatCode.encode i)) ≤ b c) (c : List Bool) :
    Ready B count D hne c (prepare B count D b c) := by
  have R := degrees_ready B count D hne hdegree c
  have S := tableRun_ready_consistent B count D b hne hdegree hheight c (prepareDegrees B count D c) (count c).size R
    (fun j _ => prepared_leaf_consistent B count D hne c j) le_rfl
  unfold prepare directions
  rw [R.source_eq]
  exact S.1

end LeanCanny.Algebra.PaddedAnnihilatorPreparation
