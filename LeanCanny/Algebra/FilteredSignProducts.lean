/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FilteredSignMoments
public import LeanCanny.Encoding.TernaryOnes

/-! # Native products of selected signs on a filtered root set -/

@[expose] public section
namespace LeanCanny.Algebra.FilteredSignProductBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation SignPatternBits
open scoped Classical BigOperators

noncomputable def value (F G : Family) (c : List Bool) : ℤ :=
  ∑ x ∈ acceptedRoots F c, ∏ i ∈ Finset.range (Nat.fromBitsLE (G.count c)),
    (SignType.sign (((G.polynomial c i).map (algebraMap ℤ ℝ)).eval x) : ℤ)

def query (G : Family) (c : List Bool) : List Bool := pair c (Ternary.ones (G.count c))

theorem query_FP {G : Family} (hG : ControlsPolyTime G) : query G ∈ FP :=
  mem_FP_pair id_mem_FP (Ternary.ones_FP hG.count hG.countUnary)

theorem moment_eq_value (F G : Family) (c : List Bool) :
    FilteredSignMomentBits.moment F G (query G c) = value F G c := by
  simp only [FilteredSignMomentBits.moment, query, pairFst_pair, pairSnd_pair,
    Ternary.ones_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits, value]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.prod_congr rfl
  intro i hi
  rw [Ternary.exponent_ones _ _ (Finset.mem_range.mp hi)]
  exact pow_one _

theorem abs_le_count (F G : Family) (c : List Bool) : (value F G c).natAbs ≤ rootCount F c := by
  rw [← moment_eq_value]
  simpa only [query, pairFst_pair] using FilteredSignMomentBits.moment_abs_le_count F G (query G c)

theorem evaluator {F G : Family} (A : Access F) (B : Access G)
    (hF : ControlsPolyTime F) (hG : ControlsPolyTime G) (hs : A.pattern ∈ FP)
    (H : SpaceFunction A.rootCoefficient) (P : SpaceFunction A.polynomialCoefficient)
    (Q : SpaceFunction B.polynomialCoefficient) :
    SpaceFunction (fun c => SignStatisticBits.integerCode (value F G c)) := by
  have E := (FilteredSignMomentBits.evaluator A B hF hG hs H P Q).precompose (query G) (query_FP hG)
  exact E.congr (funext fun c => congrArg SignStatisticBits.integerCode (moment_eq_value F G c))

end LeanCanny.Algebra.FilteredSignProductBits
