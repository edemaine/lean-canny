/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PreprocessedPairProperties
public import LeanCanny.Algebra.CannyResultantBudget

/-! # An FP height bound for the selected preprocessed pair

Only the original input degrees and heights enter the bound. The computed
square-free degrees and separating direction need not be polynomial-time.
-/

@[expose] public section

namespace LeanCanny.Algebra.PreprocessedPair
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)

noncomputable def outputHeight (F G : Family) (c : List Bool) : ℕ :=
  CannyResultantBits.coefficientBudget (F.polynomial c).natDegree (G.polynomial c).natDegree
    (((F.polynomial c).natDegree * (G.polynomial c).natDegree) ^ 2)
    (SeparableBits.squarefreeBudget F c) (SeparableBits.squarefreeBudget G c)

theorem outputHeight_binary (F G : Family) (A : Readers F) (B : Readers G) : BinaryFn (outputHeight F G) := by
  have hm : BinaryFn (fun c => (F.polynomial c).natDegree) :=
    BinaryFn.of_bits (mem_FP_of_eq A.degreeFP A.degree_eq)
  have hn : BinaryFn (fun c => (G.polynomial c).natDegree) :=
    BinaryFn.of_bits (mem_FP_of_eq B.degreeFP B.degree_eq)
  have hd : BinaryFn (fun c => ((F.polynomial c).natDegree * (G.polynomial c).natDegree) ^ 2) := by
    simpa only [pow_two] using (hm.mul hn).mul (hm.mul hn)
  have hf : BinaryFn (SeparableBits.squarefreeBudget F) := BinaryFn.of_bits
    (mem_FP_of_eq (SeparableBits.squarefreeBudgetCode_FP F A) (SeparableBits.squarefreeBudgetCode_eq F A))
  have hg : BinaryFn (SeparableBits.squarefreeBudget G) := BinaryFn.of_bits
    (mem_FP_of_eq (SeparableBits.squarefreeBudgetCode_FP G B) (SeparableBits.squarefreeBudgetCode_eq G B))
  exact CannyResultantBits.coefficientBudget_binary hm hn hd hf hg

variable (F G : Family) (A : Readers F) (B : Readers G)
variable (hF : ∀ c, F.polynomial c ≠ 0) (hG : ∀ c, G.polynomial c ≠ 0)

theorem parameter_coefficient_size (c : List Bool) (k : ℕ) :
    ((parameter F G A B hF hG c).coeff k).natAbs.size ≤ outputHeight F G c :=
  CannyResultantBits.coefficient_size_le _ _ _ _ _ _ _ _ k
    (reduced_degree_le F c (hF c)) (reduced_degree_le G c (hG c)) (direction_le F G A B hF hG c)
    (fun i => (Nat.size_le.mp (SeparableBits.squarefree_coefficient_size F c i)).le)
    (fun i => (Nat.size_le.mp (SeparableBits.squarefree_coefficient_size G c i)).le)

theorem parameter_coefficient_bound (c : List Bool) (k : ℕ) :
    ((parameter F G A B hF hG c).coeff k).natAbs ≤ 2 ^ outputHeight F G c :=
  (Nat.size_le.mp (parameter_coefficient_size F G A B hF hG c k)).le

noncomputable def outputFamily : Family where
  polynomial := parameter F G A B hF hG
  height := outputHeight F G
  coefficient_bound := parameter_coefficient_bound F G A B hF hG

end LeanCanny.Algebra.PreprocessedPair
