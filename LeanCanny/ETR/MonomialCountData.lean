/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.IndexedExpansion
public import LeanCanny.ETR.NNFEncoding
import Mathlib.Tactic.Linarith

/-!
# Monomial counts on arbitrary raw syntax trees

Only three-child nodes tagged as addition or multiplication combine counts.
Every other node has count one. On ETR terms this agrees with the indexed
expansion. The binary count length is linear in raw tree size, including on
malformed syntax; this bounds every frame of the encoded tree fold.
-/

@[expose] public section

namespace LeanCanny.ETR.MonomialCount


def countData : Data → ℕ
  | .l [tag, a, b] =>
    if tag = Codec.unary 2 then countData a + countData b
    else if tag = Codec.unary 3 then countData a * countData b else 1
  | _ => 1

theorem countData_term (t : Term) : countData t.toData = t.monomialCount := by
  induction t <;> simp_all [countData, Term.toData, Term.monomialCount, Codec.unary]

theorem countData_le_pow (d : Data) : countData d ≤ 2 ^ d.size := by
  induction d using Data.inductionChildren with
  | node xs ih =>
    rcases xs with _ | ⟨tag, _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩⟩
    · exact Nat.one_le_two_pow
    · exact Nat.one_le_two_pow
    · exact Nat.one_le_two_pow
    · have ha := ih a (by simp)
      have hb := ih b (by simp)
      have hdeg : a.size + b.size + 1 ≤ (Data.l [tag, a, b]).size := by
        simp only [Data.cons_size, Data.size_empty]
        omega
      have hsum : 2 ^ a.size + 2 ^ b.size ≤ 2 ^ (a.size + b.size + 1) := by
        rw [pow_succ, pow_add]
        have hA : 1 ≤ 2 ^ a.size := Nat.one_le_two_pow
        have hB : 1 ≤ 2 ^ b.size := Nat.one_le_two_pow
        nlinarith
      simp only [countData]
      split_ifs
      · exact (Nat.add_le_add ha hb).trans (hsum.trans (Nat.pow_le_pow_right (by decide) hdeg))
      · exact (Nat.mul_le_mul ha hb).trans (by
          rw [← pow_add]
          exact Nat.pow_le_pow_right (by decide) (by omega))
      · exact Nat.one_le_two_pow
    · exact Nat.one_le_two_pow

theorem countData_size_le (d : Data) : (countData d).size ≤ d.size + 1 := by
  simpa only [Nat.size_pow] using Nat.size_le_size (countData_le_pow d)

end LeanCanny.ETR.MonomialCount
