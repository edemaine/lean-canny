/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleCuts
public import LeanCanny.Algebra.IntegerRootSeparation
public import LeanCanny.Algebra.DyadicIsolatingInterval
public import LeanCanny.Algebra.RationalIsolatingInterval

/-! # Source-derived isolation certificates for the actual critical samples

Every sample has an isolating dyadic cell whose lower and upper cut counts
are its ordered rank and rank plus one. The precision and numerator-size
allowances have native binary writers. The numerator itself is only an
existential certificate and is not asserted to have polynomial word length.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleIsolation
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open scoped Classical
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameter

noncomputable def precision (P : Readers) (c : List Bool) : ℕ := IntegerRootSeparation.precision
  (BoundedCriticalRationalCoordinates.parameterDegree P c + 1) (BoundedCriticalRationalCoordinates.baseHeight P c)
noncomputable def indexBits (P : Readers) (c : List Bool) : ℕ :=
  precision P c + BoundedCriticalRationalCoordinates.baseHeight P c + 2

theorem precision_binary {P : Readers} (h : P.PolyTime) : BinaryFn (precision P) :=
  IntegerRootSeparation.precision_binary ((BoundedCriticalRationalCoordinates.parameterDegree_binary h).add (BinaryFn.const 1))
    (BoundedCriticalRationalCoordinates.baseHeight_binary h)
theorem indexBits_binary {P : Readers} (h : P.PolyTime) : BinaryFn (indexBits P) :=
  ((precision_binary h).add (BoundedCriticalRationalCoordinates.baseHeight_binary h)).add (BinaryFn.const 2)

theorem eval_root (P : Readers) (c : List Bool) (theta : ℝ) (ht : theta ∈ BoundedCriticalSampleLabels.rootSet P c) :
    (BoundedCriticalRationalCoordinates.parameter P c).eval₂ (Int.castRingHom ℝ) theta = 0 :=
  ((BoundedCriticalSampleLabels.mem_rootSet P c theta).mp ht).1

theorem separated (P : Readers) (c : List Bool) (a b : ℝ)
    (ha : a ∈ BoundedCriticalSampleLabels.rootSet P c) (hb : b ∈ BoundedCriticalSampleLabels.rootSet P c) (hab : a ≠ b) :
    ((2 : ℝ) ^ precision P c)⁻¹ < |a - b| :=
  IntegerRootSeparation.separated (BoundedCriticalRationalCoordinates.parameter P c)
    (BoundedCriticalRationalCoordinates.parameter_ne_zero P c)
    (BoundedCriticalRationalCoordinates.parameterDegree P c + 1) (BoundedCriticalRationalCoordinates.baseHeight P c)
    ((BoundedCriticalRationalCoordinates.parameter_bounds P c).1.trans (Nat.le_succ _))
    (fun k => (coeff_natAbs_le_coefficientMass _ k).trans (BoundedCriticalRationalCoordinates.parameter_bounds P c).2)
    a b hab (eval_root P c a ha) (eval_root P c b hb)

theorem abs_root (P : Readers) (c : List Bool) (theta : ℝ) (ht : theta ∈ BoundedCriticalSampleLabels.rootSet P c) :
    |theta| < (2 : ℝ) ^ (BoundedCriticalRationalCoordinates.baseHeight P c + 1) := by
  have H := abs_root_lt_coefficientMass_add_one (BoundedCriticalRationalCoordinates.parameter P c)
    (BoundedCriticalRationalCoordinates.parameter_ne_zero P c) theta (eval_root P c theta ht)
  have hm : coefficientMass (BoundedCriticalRationalCoordinates.parameter P c) + 1 ≤
      2 ^ (BoundedCriticalRationalCoordinates.baseHeight P c + 1) := by
    have := (BoundedCriticalRationalCoordinates.parameter_bounds P c).2
    have := Nat.one_le_two_pow (n := BoundedCriticalRationalCoordinates.baseHeight P c)
    rw [pow_succ]
    omega
  exact H.trans_le (by exact_mod_cast hm)

theorem isolating_grid (P : Readers) (c : List Bool) (theta : ℝ) (ht : theta ∈ BoundedCriticalSampleLabels.rootSet P c) :
    ∃ k : ℤ, (DyadicIsolatingInterval.lower k (precision P c) : ℝ) ≤ theta ∧
      theta < (DyadicIsolatingInterval.upper k (precision P c) : ℝ) ∧
      (BoundedCriticalSampleLabels.rootSet P c).filter (fun t => t < (DyadicIsolatingInterval.lower k (precision P c) : ℝ)) =
        (BoundedCriticalSampleLabels.rootSet P c).filter (fun t => t < theta) ∧
      (BoundedCriticalSampleLabels.rootSet P c).filter (fun t => t < (DyadicIsolatingInterval.upper k (precision P c) : ℝ)) =
        insert theta ((BoundedCriticalSampleLabels.rootSet P c).filter (fun t => t < theta)) :=
  DyadicIsolatingInterval.isolates (BoundedCriticalSampleLabels.rootSet P c) (precision P c)
    (fun a ha b hb hab => separated P c a b ha hb hab) theta ht

theorem sample_certificate (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    ∃ k : ℤ, k.natAbs.size ≤ indexBits P c ∧
      BoundedCriticalSampleCuts.count P (pair c (RationalCutBits.payload (DyadicIsolatingInterval.lower k (precision P c)))) =
        BoundedCriticalSampleLabels.rank P c x ∧
      BoundedCriticalSampleCuts.count P (pair c (RationalCutBits.payload (DyadicIsolatingInterval.upper k (precision P c)))) =
        BoundedCriticalSampleLabels.rank P c x + 1 := by
  let theta := BoundedCriticalSampleLabels.parameter P c x
  obtain ⟨k, hl, hu, hL, hU⟩ := isolating_grid P c theta.val theta.property
  have hb := DyadicIsolatingInterval.index_size k (precision P c)
    (BoundedCriticalRationalCoordinates.baseHeight P c + 1) theta.val hl hu (abs_root P c theta.val theta.property)
  refine ⟨k, by simpa only [indexBits, Nat.add_assoc, Nat.reduceAdd] using hb, ?_, ?_⟩
  · simp only [BoundedCriticalSampleCuts.count, pairFst_pair, RationalCutBits.threshold_payload]
    rw [hL, ← BoundedCriticalSampleLabels.rank_eq_card_below P c x]
  · simp only [BoundedCriticalSampleCuts.count, pairFst_pair, RationalCutBits.threshold_payload]
    rw [hU, Finset.card_insert_of_notMem]
    · rw [← BoundedCriticalSampleLabels.rank_eq_card_below P c x]
    · simp only [Finset.mem_filter, lt_self_iff_false, and_false, not_false_eq_true]

end LeanCanny.Encoding.BoundedCriticalSampleIsolation
