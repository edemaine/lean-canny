/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ResultantBounds
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Monotone binary height controls for Canny resultants

Upper bounds on the degrees and direction suffice; neither their exact values
nor their polynomial-time computation is required for this height writer.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyResultantBits

def coefficientBudget (m n d b₁ b₂ : ℕ) : ℕ :=
  (m + n).size * (m + n) + n * ((m + 1).size + m + (b₁ + 1) + (d + 1).size * m) + m * (b₂ + 1) + 1

theorem coefficientBudget_mono {m n d b₁ b₂ M N D B₁ B₂ : ℕ}
    (hm : m ≤ M) (hn : n ≤ N) (hd : d ≤ D) (hb₁ : b₁ ≤ B₁) (hb₂ : b₂ ≤ B₂) :
    coefficientBudget m n d b₁ b₂ ≤ coefficientBudget M N D B₁ B₂ := by
  unfold coefficientBudget
  gcongr <;> apply Nat.size_le_size <;> omega

theorem coefficient_size_le (p q : Polynomial ℤ) (d M N D b₁ b₂ k : ℕ)
    (hm : p.natDegree ≤ M) (hn : q.natDegree ≤ N) (hd : d ≤ D)
    (hp : ∀ i, (p.coeff i).natAbs ≤ 2 ^ b₁) (hq : ∀ i, (q.coeff i).natAbs ≤ 2 ^ b₂) :
    ((cannyResultant p q d).coeff k).natAbs.size ≤ coefficientBudget M N D b₁ b₂ := by
  have h := cannyResultant_coeff_size_le p q d (2 ^ b₁) (2 ^ b₂) k hp hq
  have h' : ((cannyResultant p q d).coeff k).natAbs.size ≤ coefficientBudget p.natDegree q.natDegree d b₁ b₂ := by
    simpa only [coefficientBudget, shiftBitBudget, Nat.size_pow] using h
  exact h'.trans (coefficientBudget_mono hm hn hd le_rfl le_rfl)

theorem coefficientBudget_binary {m n d b₁ b₂ : List Bool → ℕ}
    (hm : BinaryFn m) (hn : BinaryFn n) (hd : BinaryFn d) (hb₁ : BinaryFn b₁) (hb₂ : BinaryFn b₂) :
    BinaryFn (fun c => coefficientBudget (m c) (n c) (d c) (b₁ c) (b₂ c)) :=
  (((hm.add hn).size.mul (hm.add hn)).add
    (hn.mul ((((hm.add (BinaryFn.const 1)).size.add hm).add (hb₁.add (BinaryFn.const 1))).add
      ((hd.add (BinaryFn.const 1)).size.mul hm)))).add (hm.mul (hb₂.add (BinaryFn.const 1))) |>.add (BinaryFn.const 1)

end LeanCanny.Algebra.CannyResultantBits
