/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialLocalSign

/-! # A native bounded scan for the first nonzero sign tag

Only the current two-bit sign is retained. The supplied binary count may
be exponential; every child sign computation is charged to the space bound.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialLocalSignBits
open LeanCanny.Computation LeanCanny.Encoding

def value (f count : List Bool → List Bool) (q : List Bool) : List Bool :=
  BoundedFold.fold (InfinitesimalSign.update f) (fun _ => []) q (Nat.fromBitsLE (count q))

theorem fold_length (f : List Bool → List Bool) (hf : ∀ q, (f q).length ≤ 2) (q : List Bool) (n : ℕ) :
    (BoundedFold.fold (InfinitesimalSign.update f) (fun _ => []) q n).length ≤ 2 := by
  induction n with
  | zero => simp only [BoundedFold.fold, List.length_nil, Nat.zero_le]
  | succ n ih =>
    rw [BoundedFold.fold, InfinitesimalSign.update, InfinitesimalSign.finish]
    simp only [pairFst_pair, pairSnd_pair, BoundedFold.accumulator_packet]
    split_ifs
    · exact hf _
    · exact ih

theorem evaluator {f count : List Bool → List Bool} (E : SpaceFunction f) (hc : count ∈ FP)
    (hf : ∀ q, (f q).length ≤ 2) : SpaceFunction (value f count) :=
  BoundedFold.evaluator (InfinitesimalSign.updateEvaluator E) count (fun _ => []) hc (constFn_mem_FP []) 2
    (fun q n _ => by simpa only [Polynomial.eval_ofNat] using fold_length f hf q n)

theorem packet (f count : List Bool → List Bool) (q : List Bool) (a : ℕ → ℤ)
    (hf : ∀ k, f (pair q (BinaryNatCode.encode k)) = InfinitesimalSign.tag (a k)) :
    value f count q = InfinitesimalSign.scan a (Nat.fromBitsLE (count q)) :=
  InfinitesimalSign.fold_eq_scan f q a hf _

end LeanCanny.Algebra.PolynomialLocalSignBits
