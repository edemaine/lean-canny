/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Adapted for lean-canny from TauCeti at revision 034e577c895d28c058d92af4036f7ce0b03081cf.
Source: Data/Nat/Choose/Basic.lean.
Changes: selected algebraic proof slice, project namespace, and pinned Mathlib
compatibility. See STURM_SOURCES.md.
-/
module

public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! # Algebraic principal subresultant identities

Adapted proof slice for the signed determinant formula used in Sturm–Tarski queries.
See STURM_SOURCES.md for the upstream source and omitted material.
-/

public section

namespace LeanCanny.Algebra.PrincipalSubresultant

open List

section

/-- The second binomial coefficient of a sum: `C(m + n, 2) = C(m, 2) + C(n, 2) + mn`. -/
theorem add_choose_two (m n : ℕ) : (m + n).choose 2 = m.choose 2 + n.choose 2 + m * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : (m + (n + 1)).choose 2 = (m + n).choose 1 + (m + n).choose 2 := by
        rw [← Nat.add_assoc]
        exact Nat.choose_succ_succ (m + n) 1
      have h2 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
      rw [h1, h2, ih, Nat.choose_one_right, Nat.choose_one_right]
      ring

end

end LeanCanny.Algebra.PrincipalSubresultant
