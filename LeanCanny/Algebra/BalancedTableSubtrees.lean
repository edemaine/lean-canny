/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedAnnihilatorPreparation
public import LeanCanny.Algebra.BalancedSubtreeLocality

/-! # Every subtree of a completely prepared table is consistent -/

@[expose] public section

namespace LeanCanny.Algebra.BalancedTablePolynomials
open LeanCanny.Encoding
open SeparableBits (Family)

theorem Consistent.subtree (B : Family) (f : List Bool) (leaves : ℕ → SeparableIntegerPolynomial)
    (N : ℕ) (hc : Consistent B f leaves N 0) (h i : ℕ) (hh : h ≤ N) (hi : i < 2 ^ (N - h)) :
    Consistent B f leaves h i :=
  BalancedSubtreeLocality.consistent_subtree B f leaves N h i hh hi hc

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
