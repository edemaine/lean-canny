/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PreprocessedPairBounds
public import LeanCanny.Algebra.PrimitivePairBounds

/-! # Source-derived degree and mass bounds for computed pair coordinates -/

@[expose] public section

namespace LeanCanny.Algebra.CannyResultantBits

def coordinateMassBudget (m n d b₁ b₂ : ℕ) : ℕ :=
  coefficientBudget m n d b₁ b₂ + ((m + 1).size + m + (b₁ + 1) + (d + 1).size * m) +
    (b₂ + 1) + 1 + (m * n + 2).size + d.size

theorem massBudget_le {m n d M N D : ℕ} (b₁ b₂ : ℕ) (hm : m ≤ M) (hn : n ≤ N) (hd : d ≤ D) :
    PrimitivePair.massBudget m n d (2 ^ b₁) (2 ^ b₂) ≤ coordinateMassBudget M N D b₁ b₂ := by
  have hfull := Subresultant.budget_le_full m n 1 (shiftBitBudget m d (2 ^ b₁)) (2 ^ b₂).size
  have hb : coordinateBitBudget m n d (2 ^ b₁) (2 ^ b₂) ≤
      coefficientBudget m n d b₁ b₂ + shiftBitBudget m d (2 ^ b₁) + (b₂ + 1) + 1 := by
    simp only [Nat.size_pow] at hfull
    simp only [coordinateBitBudget, coefficientBudget, shiftBitBudget, Nat.size_pow] at *
    omega
  have hc := coefficientBudget_mono hm hn hd (le_refl b₁) (le_refl b₂)
  have hs : shiftBitBudget m d (2 ^ b₁) ≤ shiftBitBudget M D (2 ^ b₁) := by
    unfold shiftBitBudget
    gcongr <;> apply Nat.size_le_size <;> omega
  have hp : (n - 1) * m ≤ M * N := by
    exact (Nat.mul_le_mul ((Nat.sub_le n 1).trans hn) hm).trans_eq (Nat.mul_comm N M)
  have hg : (max 1 ((n - 1) * m) + 1).size ≤ (M * N + 2).size := Nat.size_le_size (by omega)
  have hd' := Nat.size_le_size hd
  unfold PrimitivePair.massBudget coordinateMassBudget
  simp only [shiftBitBudget, Nat.size_pow] at hs hb
  omega

theorem coordinateMassBudget_binary {m n d b₁ b₂ : List Bool → ℕ}
    (hm : BinaryFn m) (hn : BinaryFn n) (hd : BinaryFn d) (hb₁ : BinaryFn b₁) (hb₂ : BinaryFn b₂) :
    BinaryFn (fun c => coordinateMassBudget (m c) (n c) (d c) (b₁ c) (b₂ c)) := by
  have hs := (((hm.add (BinaryFn.const 1)).size.add hm).add (hb₁.add (BinaryFn.const 1))).add
    ((hd.add (BinaryFn.const 1)).size.mul hm)
  exact (((((coefficientBudget_binary hm hn hd hb₁ hb₂).add hs).add (hb₂.add (BinaryFn.const 1))).add
    (BinaryFn.const 1)).add ((hm.mul hn).add (BinaryFn.const 2)).size).add hd.size

end LeanCanny.Algebra.CannyResultantBits

namespace LeanCanny.Algebra.PreprocessedPair
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)

noncomputable def coordinateHeight (F G : Family) (c : List Bool) : ℕ :=
  CannyResultantBits.coordinateMassBudget (F.polynomial c).natDegree (G.polynomial c).natDegree
    (((F.polynomial c).natDegree * (G.polynomial c).natDegree) ^ 2)
    (SeparableBits.squarefreeBudget F c) (SeparableBits.squarefreeBudget G c)

theorem coordinateHeight_binary (F G : Family) (A : Readers F) (B : Readers G) : BinaryFn (coordinateHeight F G) := by
  have hm : BinaryFn (fun c => (F.polynomial c).natDegree) := BinaryFn.of_bits (mem_FP_of_eq A.degreeFP A.degree_eq)
  have hn : BinaryFn (fun c => (G.polynomial c).natDegree) := BinaryFn.of_bits (mem_FP_of_eq B.degreeFP B.degree_eq)
  have hd : BinaryFn (fun c => ((F.polynomial c).natDegree * (G.polynomial c).natDegree) ^ 2) := by
    simpa only [pow_two] using (hm.mul hn).mul (hm.mul hn)
  have hf : BinaryFn (SeparableBits.squarefreeBudget F) := BinaryFn.of_bits
    (mem_FP_of_eq (SeparableBits.squarefreeBudgetCode_FP F A) (SeparableBits.squarefreeBudgetCode_eq F A))
  have hg : BinaryFn (SeparableBits.squarefreeBudget G) := BinaryFn.of_bits
    (mem_FP_of_eq (SeparableBits.squarefreeBudgetCode_FP G B) (SeparableBits.squarefreeBudgetCode_eq G B))
  exact CannyResultantBits.coordinateMassBudget_binary hm hn hd hf hg

variable (F G : Family) (A : Readers F) (B : Readers G)
variable (hF : ∀ c, F.polynomial c ≠ 0) (hG : ∀ c, G.polynomial c ≠ 0)

theorem coordinate_mass (c : List Bool) :
    coefficientMass (leftNumerator F G A B hF hG c) ≤ 2 ^ coordinateHeight F G c ∧
    coefficientMass (rightNumerator F G A B hF hG c) ≤ 2 ^ coordinateHeight F G c ∧
    coefficientMass (denominator F G A B hF hG c) ≤ 2 ^ coordinateHeight F G c := by
  have h := PrimitivePair.coordinate_mass (reduced F c) (reduced G c) (direction F G A B hF hG c)
    (2 ^ SeparableBits.squarefreeBudget F c) (2 ^ SeparableBits.squarefreeBudget G c)
    (fun i => (Nat.size_le.mp (SeparableBits.squarefree_coefficient_size F c i)).le)
    (fun i => (Nat.size_le.mp (SeparableBits.squarefree_coefficient_size G c i)).le)
  have hb := Nat.pow_le_pow_right (n := 2) (by decide) (CannyResultantBits.massBudget_le
    (SeparableBits.squarefreeBudget F c) (SeparableBits.squarefreeBudget G c)
    (reduced_degree_le F c (hF c)) (reduced_degree_le G c (hG c)) (direction_le F G A B hF hG c))
  exact ⟨h.1.trans hb, h.2.1.trans hb, h.2.2.trans hb⟩

theorem coordinate_degrees (c : List Bool) :
    (leftNumerator F G A B hF hG c).natDegree ≤ (F.polynomial c).natDegree * (G.polynomial c).natDegree + 2 ∧
    (rightNumerator F G A B hF hG c).natDegree ≤ (F.polynomial c).natDegree * (G.polynomial c).natDegree + 2 ∧
    (denominator F G A B hF hG c).natDegree ≤ (F.polynomial c).natDegree * (G.polynomial c).natDegree + 2 := by
  have hp : ((reduced G c).natDegree - 1) * (reduced F c).natDegree ≤
      (F.polynomial c).natDegree * (G.polynomial c).natDegree :=
    (Nat.mul_le_mul ((Nat.sub_le _ _).trans (reduced_degree_le G c (hG c)))
      (reduced_degree_le F c (hF c))).trans_eq (Nat.mul_comm _ _)
  have hl := PrimitivePair.leftNumerator_degree (reduced F c) (reduced G c) (direction F G A B hF hG c)
  have hr := PrimitivePair.rightNumerator_degree (reduced F c) (reduced G c) (direction F G A B hF hG c)
  have hd := PrimitivePair.denominator_degree (reduced F c) (reduced G c) (direction F G A B hF hG c)
  exact ⟨hl.trans (by omega), hr.trans (by omega), hd.trans (by omega)⟩

end LeanCanny.Algebra.PreprocessedPair
