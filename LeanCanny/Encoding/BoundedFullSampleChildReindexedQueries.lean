/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildQueries

/-! # Regular-child moments with a preserved source context

Record and matrix queries add fields to the original source. Reindexing the
two native filters preserves that source while allowing selected probes to
depend on the whole query.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildReindexedQueries
open LeanCanny.Algebra LeanCanny.Computation
open BoundedFullSampleChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildCoordinates.parameter
  BoundedFullSampleChildFilters.polynomial BoundedFullSampleChildRegularFilter.polynomial
  BoundedFullSampleChildSingularCount.test PrimitivePairBits.coefficient

noncomputable def moment (F : Inputs) (context : List Bool → List Bool) (G : SignPatternBits.Family) (z : List Bool) : ℤ :=
  ∑ theta ∈ BoundedFullSampleChildQueries.roots F (context z), BoundedFullSampleChildQueries.product G z theta

theorem moment_eq_difference (F : Inputs) (context : List Bool → List Bool) (G : SignPatternBits.Family) (z : List Bool) :
    moment F context G z =
      FilteredSignProductBits.value ((BoundedFullSampleChildEquationCount.family F).comp context) G z -
        FilteredSignProductBits.value ((BoundedFullSampleChildSingularCount.family F).comp context) G z := by
  have he (H : SignPatternBits.Family) : SignPatternBits.acceptedRoots (H.comp context) z =
      SignPatternBits.acceptedRoots H (context z) := rfl
  simp only [FilteredSignProductBits.value, he, BoundedFullSampleChildQueries.equation_accepted,
    BoundedFullSampleChildQueries.singular_accepted]
  change (∑ theta ∈ BoundedFullSampleChildQueries.roots F (context z), BoundedFullSampleChildQueries.product G z theta) =
    (∑ theta ∈ BoundedFullSampleChildRegularCount.equationRoots F (context z), BoundedFullSampleChildQueries.product G z theta) -
      ∑ theta ∈ (BoundedFullSampleChildRegularCount.equationRoots F (context z)).filter
        (fun theta => (BoundedFullSampleChildRegularFilter.polynomial F (context z)).eval₂ (Int.castRingHom ℝ) theta = 0),
          BoundedFullSampleChildQueries.product G z theta
  have H := Finset.sum_filter_add_sum_filter_not (BoundedFullSampleChildRegularCount.equationRoots F (context z))
    (fun theta => (BoundedFullSampleChildRegularFilter.polynomial F (context z)).eval₂ (Int.castRingHom ℝ) theta = 0)
    (BoundedFullSampleChildQueries.product G z)
  simp only [BoundedFullSampleChildQueries.roots, ne_eq]
  omega

theorem evaluator {F : Inputs} (h : F.PolyTime) {context : List Bool → List Bool} (hc : context ∈ FP)
    {G : SignPatternBits.Family} (A : SignPatternBits.Access G) (hG : SignPatternBits.ControlsPolyTime G)
    (Q : SpaceFunction A.polynomialCoefficient) :
    SpaceFunction (fun z => SignStatisticBits.integerCode (moment F context G z)) := by
  have hq := SignPatternBits.compQuery_FP hc
  have R := (BoundedFullSampleChildCoordinates.parameter_coefficient_evaluator h).precompose
    (SignPatternBits.compQuery context) hq
  have P := ((BoundedFullSampleChildFilters.evaluator h).precompose
    BoundedFullSampleChildEquationCount.filterQuery BoundedFullSampleChildEquationCount.filterQuery_FP).precompose
      (SignPatternBits.compQuery context) hq
  have S := ((BoundedFullSampleChildSingularCount.test_evaluator h).precompose
    BoundedFullSampleChildReaders.query BoundedFullSampleChildReaders.query_FP).precompose
      (SignPatternBits.compQuery context) hq
  have hs : ((BoundedFullSampleChildEquationCount.access F).comp context).pattern ∈ FP := by
    change ((BoundedFullSampleChildEquationCount.access F).pattern ∘ SignPatternBits.compPattern context) ∈ FP
    exact mem_FP_comp (SignPatternBits.compPattern_FP hc) (constFn_mem_FP [])
  have ht : ((BoundedFullSampleChildSingularCount.access F).comp context).pattern ∈ FP := by
    change ((BoundedFullSampleChildSingularCount.access F).pattern ∘ SignPatternBits.compPattern context) ∈ FP
    exact mem_FP_comp (SignPatternBits.compPattern_FP hc) (constFn_mem_FP [])
  have E := FilteredSignProductBits.evaluator ((BoundedFullSampleChildEquationCount.access F).comp context) A
    (SignPatternBits.comp_controls (BoundedFullSampleChildEquationCount.controls h) hc) hG hs R P Q
  have T := FilteredSignProductBits.evaluator ((BoundedFullSampleChildSingularCount.access F).comp context) A
    (SignPatternBits.comp_controls (BoundedFullSampleChildSingularCount.controls h) hc) hG ht R S Q
  exact (IntegerDifferenceBits.evaluator E T).congr (funext fun z =>
    congrArg SignStatisticBits.integerCode (moment_eq_difference F context G z).symm)

theorem moment_bound (F : Inputs) (context : List Bool → List Bool) (G : SignPatternBits.Family) (z : List Bool) :
    (moment F context G z).natAbs ≤ BoundedFullSampleChildRegularCount.count F (context z) := by
  rw [← BoundedFullSampleChildQueries.roots_card, moment]
  apply (Int.natAbs_sum_le _ _).trans
  calc
    _ ≤ ∑ _theta ∈ BoundedFullSampleChildQueries.roots F (context z), 1 := by
      apply Finset.sum_le_sum
      intro theta _
      change Int.natAbsHom _ ≤ 1
      rw [BoundedFullSampleChildQueries.product, map_prod]
      apply (Finset.prod_le_prod (fun i _ => ?_)).trans_eq (Finset.prod_const_one)
      cases SignType.sign (((G.polynomial z i).map (algebraMap ℤ ℝ)).eval theta) <;> decide
    _ = _ := by simp

end LeanCanny.Encoding.BoundedFullSampleChildReindexedQueries
