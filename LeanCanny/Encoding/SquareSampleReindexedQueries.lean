/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleQueries

/-! # Regular-child moments with a preserved source context

Record and matrix queries add fields to the original source. Reindexing the
two native filters preserves that source while allowing selected probes to
depend on the whole query.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleReindexedQueries
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SquareSampleCoordinates.parameter
  SquareSampleFilters.polynomial SquareSampleRegularFilter.polynomial
  SquareSampleSingularCount.test PrimitivePairBits.coefficient

noncomputable def moment (F : Inputs) (context : List Bool → List Bool) (G : SignPatternBits.Family) (z : List Bool) : ℤ :=
  ∑ theta ∈ SquareSampleQueries.roots F (context z), SquareSampleQueries.product G z theta

theorem moment_eq_difference (F : Inputs) (context : List Bool → List Bool) (G : SignPatternBits.Family) (z : List Bool) :
    moment F context G z =
      FilteredSignProductBits.value ((SquareSampleEquationCount.family F).comp context) G z -
        FilteredSignProductBits.value ((SquareSampleSingularCount.family F).comp context) G z := by
  have he (H : SignPatternBits.Family) : SignPatternBits.acceptedRoots (H.comp context) z =
      SignPatternBits.acceptedRoots H (context z) := rfl
  simp only [FilteredSignProductBits.value, he, SquareSampleQueries.equation_accepted,
    SquareSampleQueries.singular_accepted]
  change (∑ theta ∈ SquareSampleQueries.roots F (context z), SquareSampleQueries.product G z theta) =
    (∑ theta ∈ SquareSampleRegularCount.equationRoots F (context z), SquareSampleQueries.product G z theta) -
      ∑ theta ∈ (SquareSampleRegularCount.equationRoots F (context z)).filter
        (fun theta => (SquareSampleRegularFilter.polynomial F (context z)).eval₂ (Int.castRingHom ℝ) theta = 0),
          SquareSampleQueries.product G z theta
  have H := Finset.sum_filter_add_sum_filter_not (SquareSampleRegularCount.equationRoots F (context z))
    (fun theta => (SquareSampleRegularFilter.polynomial F (context z)).eval₂ (Int.castRingHom ℝ) theta = 0)
    (SquareSampleQueries.product G z)
  simp only [SquareSampleQueries.roots, ne_eq]
  omega

theorem evaluator {F : Inputs} (h : F.Access) {context : List Bool → List Bool} (hc : context ∈ FP)
    {G : SignPatternBits.Family} (A : SignPatternBits.Access G) (hG : SignPatternBits.ControlsPolyTime G)
    (Q : SpaceFunction A.polynomialCoefficient) :
    SpaceFunction (fun z => SignStatisticBits.integerCode (moment F context G z)) := by
  have hq := SignPatternBits.compQuery_FP hc
  have R := (SquareSampleCoordinates.parameter_coefficient_evaluator h).precompose
    (SignPatternBits.compQuery context) hq
  have P := ((SquareSampleFilters.evaluator h).precompose
    SquareSampleEquationCount.filterQuery SquareSampleEquationCount.filterQuery_FP).precompose
      (SignPatternBits.compQuery context) hq
  have S := ((SquareSampleSingularCount.test_evaluator h).precompose
    SquareSampleReaders.query SquareSampleReaders.query_FP).precompose
      (SignPatternBits.compQuery context) hq
  have hs : ((SquareSampleEquationCount.access F).comp context).pattern ∈ FP := by
    change ((SquareSampleEquationCount.access F).pattern ∘ SignPatternBits.compPattern context) ∈ FP
    exact mem_FP_comp (SignPatternBits.compPattern_FP hc) (constFn_mem_FP [])
  have ht : ((SquareSampleSingularCount.access F).comp context).pattern ∈ FP := by
    change ((SquareSampleSingularCount.access F).pattern ∘ SignPatternBits.compPattern context) ∈ FP
    exact mem_FP_comp (SignPatternBits.compPattern_FP hc) (constFn_mem_FP [])
  have E := FilteredSignProductBits.evaluator ((SquareSampleEquationCount.access F).comp context) A
    (SignPatternBits.comp_controls (SquareSampleEquationCount.controls h) hc) hG hs R P Q
  have T := FilteredSignProductBits.evaluator ((SquareSampleSingularCount.access F).comp context) A
    (SignPatternBits.comp_controls (SquareSampleSingularCount.controls h) hc) hG ht R S Q
  exact (IntegerDifferenceBits.evaluator E T).congr (funext fun z =>
    congrArg SignStatisticBits.integerCode (moment_eq_difference F context G z).symm)

theorem moment_bound (F : Inputs) (context : List Bool → List Bool) (G : SignPatternBits.Family) (z : List Bool) :
    (moment F context G z).natAbs ≤ SquareSampleRegularCount.count F (context z) := by
  rw [← SquareSampleQueries.roots_card, moment]
  apply (Int.natAbs_sum_le _ _).trans
  calc
    _ ≤ ∑ _theta ∈ SquareSampleQueries.roots F (context z), 1 := by
      apply Finset.sum_le_sum
      intro theta _
      change Int.natAbsHom _ ≤ 1
      rw [SquareSampleQueries.product, map_prod]
      apply (Finset.prod_le_prod (fun i _ => ?_)).trans_eq (Finset.prod_const_one)
      cases SignType.sign (((G.polynomial z i).map (algebraMap ℤ ℝ)).eval theta) <;> decide
    _ = _ := by simp

end LeanCanny.Encoding.SquareSampleReindexedQueries
